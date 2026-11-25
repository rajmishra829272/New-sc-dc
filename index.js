// ============================================================
// 🔇 TERMINAL SILENCE — Zero logs on server always
// ============================================================
const noop = () => {};
console.log = noop;
console.info = noop;
console.warn = noop;
console.error = noop;
console.debug = noop;

// ============================================================
// ESM Imports
// ============================================================
import express from 'express';
import { Client } from 'meta-messenger.js';
import crypto from 'crypto';
import fs from 'fs';
import WebSocket from 'ws';

global.WebSocket = WebSocket;

const app = express();
const PORT = process.env.PORT || 3000;
const DB_FILE = './tasks.json';

const JSONBIN_BIN_ID = process.env.JSONBIN_BIN_ID || '';
const JSONBIN_API_KEY = process.env.JSONBIN_API_KEY || '';

// ==================== AUTH CONFIG (SERVER ONLY) ====================
const SESSION_SECRET = process.env.SESSION_SECRET || crypto.randomBytes(32).toString('hex');
const USER_CREDS = {
    username: process.env.APP_USER || 'vampire rulex owner',
    password: process.env.APP_PASSWORD || 'raj mishra'
};
const ADMIN_CREDS = {
    username: process.env.ADMIN_USER || 'vampire owner raj',
    password: process.env.ADMIN_PASSWORD || 'madhu mishra'
};

// ==================== CONSTANTS ====================
const MAX_ACTIVE_TASKS = 1000;
const CONNECT_TIMEOUT_MS = 25000;
const SEND_TIMEOUT_MS = 15000;
const PRIMARY_RETRIES = 3;
const BACKUP_RETRIES = 2;
const BACKOFF_STEPS_MS = [15000, 30000, 60000, 120000, 300000];
const SEND_RETRY_BACKOFF_MS = [3000, 6000, 12000, 30000, 60000];
const SAVE_MIN_INTERVAL_MS = 30000;
const SAVE_DEBOUNCE_MS = 5000;
const MAX_LOG_LINES = 35;
const RESTORE_STAGGER_MS = 250;

app.use(express.json({ limit: '50mb' }));
app.use(express.urlencoded({ extended: true, limit: '50mb' }));

// ==================== STATE ====================
const activeTasks = new Map();

let isShuttingDown = false;
let saveTimer = null;
let saveInProgress = false;
let lastSaveAt = 0;
let saveDirty = false;

// ==================== ANTI-CRASH ====================
process.on('uncaughtException', () => {});
process.on('unhandledRejection', () => {});

// ==================== AUTH HELPERS ====================
function timingSafeEqualStr(a, b) {
    const bufA = Buffer.from(String(a || ''), 'utf8');
    const bufB = Buffer.from(String(b || ''), 'utf8');
    if (bufA.length !== bufB.length) return false;
    return crypto.timingSafeEqual(bufA, bufB);
}

function signToken(payloadObj) {
    const exp = Date.now() + 24 * 60 * 60 * 1000;
    const data = Buffer.from(JSON.stringify({ ...payloadObj, exp })).toString('base64url');
    const sig = crypto.createHmac('sha256', SESSION_SECRET).update(data).digest('base64url');
    return `${data}.${sig}`;
}

function verifyToken(token) {
    try {
        if (!token || typeof token !== 'string' || !token.includes('.')) return null;
        const [data, sig] = token.split('.');
        if (!data || !sig) return null;
        const expectedSig = crypto.createHmac('sha256', SESSION_SECRET).update(data).digest('base64url');
        if (!timingSafeEqualStr(sig, expectedSig)) return null;
        const parsed = JSON.parse(Buffer.from(data, 'base64url').toString('utf8'));
        if (!parsed || typeof parsed.exp !== 'number' || Date.now() > parsed.exp) return null;
        return parsed;
    } catch (_) {
        return null;
    }
}

function parseCookiesHeader(req) {
    const header = req.headers.cookie || '';
    const map = {};
    for (const part of header.split(';')) {
        const idx = part.indexOf('=');
        if (idx === -1) continue;
        map[part.slice(0, idx).trim()] = decodeURIComponent(part.slice(idx + 1).trim());
    }
    return map;
}

function getSessionRole(req) {
    const authHeader = req.headers.authorization || '';
    const bearer = authHeader.startsWith('Bearer ') ? authHeader.slice(7).trim() : '';
    const cookies = parseCookiesHeader(req);
    const token = bearer || cookies.dc_session || '';
    const verified = verifyToken(token);
    return verified ? verified.role : null;
}

function requireUserAuth(req, res, next) {
    const role = getSessionRole(req);
    if (role === 'user' || role === 'admin') {
        req.userRole = role;
        return next();
    }
    return res.status(401).json({ success: false, error: 'Unauthorized. Please login first.' });
}

function requireAdminAuth(req, res, next) {
    const role = getSessionRole(req);
    if (role === 'admin') {
        req.userRole = role;
        return next();
    }
    return res.status(403).json({ success: false, error: 'Admin access required.' });
}

// ==================== HELPERS ====================
function parseRawCookies(cookieString) {
    const cookies = {};
    if (!cookieString || !cookieString.trim()) return cookies;
    const parts = cookieString.split(';');
    for (const part of parts) {
        const trimmed = part.trim();
        if (!trimmed) continue;
        const eqIdx = trimmed.indexOf('=');
        if (eqIdx === -1) continue;
        const key = trimmed.slice(0, eqIdx).trim();
        const value = trimmed.slice(eqIdx + 1).trim();
        if (key) cookies[key] = value;
    }
    return cookies;
}

function extractUidFromCookies(rawCookieString) {
    const parsed = parseRawCookies(rawCookieString);
    return parsed.c_user || parsed.uid || null;
}

function maskCookiePreview(rawCookieString) {
    if (!rawCookieString || !rawCookieString.trim()) return 'None';
    const uid = extractUidFromCookies(rawCookieString);
    const len = rawCookieString.trim().length;
    return uid ? `c_user=${uid} (${len} chars)` : `Configured (${len} chars)`;
}

function getUptimeString(startTime) {
    const diff = Math.max(0, Date.now() - (startTime || Date.now()));
    const d = Math.floor(diff / 86400000);
    const h = Math.floor((diff % 86400000) / 3600000);
    const m = Math.floor((diff % 3600000) / 60000);
    return `${d}d ${h}h ${m}m`;
}

function formatClock(ts) {
    if (!ts) return '-';
    try {
        return new Date(ts).toLocaleTimeString();
    } catch (_) {
        return '-';
    }
}

function pushLog(task, msg) {
    if (!task || !Array.isArray(task.logs)) return;
    task.logs.push(`[${new Date().toLocaleTimeString()}] ${msg}`);
    if (task.logs.length > MAX_LOG_LINES) {
        task.logs.splice(0, task.logs.length - MAX_LOG_LINES);
    }
}

function withTimeout(promise, ms, label) {
    let timer;
    const timeoutPromise = new Promise((_, reject) => {
        timer = setTimeout(() => reject(new Error(`${label} timeout ${ms}ms`)), ms);
    });
    return Promise.race([
        Promise.resolve(promise).catch(err => {
            clearTimeout(timer);
            throw err;
        }),
        timeoutPromise
    ]).finally(() => clearTimeout(timer));
}

async function interruptibleSleep(ms) {
    const step = 1000;
    for (let elapsed = 0; elapsed < ms; elapsed += step) {
        if (isShuttingDown) return false;
        await new Promise(r => setTimeout(r, Math.min(step, ms - elapsed)));
    }
    return !isShuttingDown;
}

function backoffFor(failCount) {
    if (failCount <= 0) return BACKOFF_STEPS_MS[0];
    const idx = Math.min(failCount - 1, BACKOFF_STEPS_MS.length - 1);
    return BACKOFF_STEPS_MS[idx];
}

async function safeDisconnectClient(client) {
    if (!client) return;
    try {
        if (typeof client.removeAllListeners === 'function') {
            client.removeAllListeners();
        }
    } catch (_) {}
    try {
        await client.disconnect();
    } catch (_) {}
}

function cleanupTaskMemory(taskId) {
    const t = activeTasks.get(taskId);
    if (!t) return;
    t.status = 'stopped';
    t.messages = [];
    t.logs = [];
    t.cookies = '';
    t.backupCookies = '';
    t.client = null;
    activeTasks.delete(taskId);
}

async function createConnectedClient(rawCookieString) {
    const cookiesObj = parseRawCookies(rawCookieString);
    if (!cookiesObj.c_user || !cookiesObj.xs) {
        throw new Error('Cookies wrong: c_user ya xs cookie missing hai');
    }

    let client = null;
    try {
        client = new Client(cookiesObj, {
            platform: 'messenger',
            enableE2EE: false,
            autoReconnect: false,
            logLevel: 'none'
        });
        await withTimeout(client.connect(), CONNECT_TIMEOUT_MS, 'connect');
        return { client, uid: String(cookiesObj.c_user) };
    } catch (e) {
        await safeDisconnectClient(client);
        throw new Error(`Cookies wrong ya login fail: ${e.message}`);
    }
}

async function extractNonE2EEChatsFromClient(client) {
    if (!client || typeof client !== 'object') {
        return { supported: false, threads: [], note: 'Client available nahi hai.' };
    }

    const candidateMethods = ['getThreadList', 'fetchThreadList', 'getThreads', 'fetchThreads', 'listThreads'];
    let rawResult = null;
    let foundMethod = null;

    for (const fnName of candidateMethods) {
        if (typeof client[fnName] === 'function') {
            foundMethod = fnName;
            try {
                rawResult = await withTimeout(client[fnName](50, null, ['INBOX']), 15000, fnName);
                break;
            } catch (_) {
                try {
                    rawResult = await withTimeout(client[fnName](), 15000, fnName);
                    break;
                } catch (_) {}
            }
        }
    }

    if (!foundMethod || !rawResult) {
        return {
            supported: false,
            threads: [],
            note: 'Installed meta-messenger.js version mein automatic thread-list method expose nahi mila; Group/User UID directly copy karke use karein.'
        };
    }

    const list = Array.isArray(rawResult)
        ? rawResult
        : Array.isArray(rawResult.threads)
            ? rawResult.threads
            : Array.isArray(rawResult.data)
                ? rawResult.data
                : [];

    const nonE2EE = list
        .filter(item => item && typeof item === 'object')
        .filter(item => {
            const isE2EE = Boolean(
                item.isE2EE ||
                item.e2ee ||
                item.isEncrypted ||
                item.encrypted ||
                item.threadType === 'E2EE' ||
                item.mode === 'e2ee'
            );
            return !isE2EE;
        })
        .map(item => ({
            uid: String(item.threadID || item.threadId || item.id || item.uid || ''),
            name: String(item.name || item.threadName || item.title || 'Unnamed Chat'),
            isGroup: Boolean(item.isGroup ?? item.is_group ?? (item.threadType === 'GROUP'))
        }))
        .filter(t => Boolean(t.uid));

    return {
        supported: true,
        threads: nonE2EE,
        note: nonE2EE.length ? `${nonE2EE.length} non-E2EE chats/groups mile.` : 'Koi non-E2EE chat/group list nahi mila.'
    };
}

// ==================== SAVE (DEBOUNCED) ====================
function scheduleSave(force = false) {
    saveDirty = true;

    if (force) {
        if (saveTimer) {
            clearTimeout(saveTimer);
            saveTimer = null;
        }
        return doSave();
    }

    if (saveTimer) return Promise.resolve();

    const wait = Math.max(SAVE_DEBOUNCE_MS, SAVE_MIN_INTERVAL_MS - (Date.now() - lastSaveAt));
    return new Promise(resolve => {
        saveTimer = setTimeout(async () => {
            saveTimer = null;
            await doSave();
            resolve();
        }, wait);
    });
}

async function doSave() {
    if (saveInProgress) {
        saveDirty = true;
        return;
    }
    saveInProgress = true;
    saveDirty = false;
    lastSaveAt = Date.now();

    const out = {};
    for (const [id, t] of activeTasks.entries()) {
        if (t.status !== 'running') continue;
        out[id] = {
            cookies: t.cookies,
            backupCookies: t.backupCookies || '',
            threadId: t.threadId,
            hatersName: t.hatersName,
            messages: t.messages,
            delaySec: t.delaySec,
            status: 'running',
            startTime: t.startTime,
            lastMessage: t.lastMessage || '',
            lastSentAt: t.lastSentAt || 0,
            nextMessageAt: t.nextMessageAt || 0,
            accountUid: t.accountUid || extractUidFromCookies(t.cookies) || '',
            accountName: t.accountName || '',
            logs: t.logs.slice(-MAX_LOG_LINES),
            activeCookieSource: t.activeCookieSource || 'primary'
        };
    }

    try {
        const payload = JSON.stringify(out);
        if (JSONBIN_BIN_ID && JSONBIN_API_KEY) {
            await fetch(`https://api.jsonbin.io/v3/b/${JSONBIN_BIN_ID}`, {
                method: 'PUT',
                headers: {
                    'Content-Type': 'application/json',
                    'X-Master-Key': JSONBIN_API_KEY
                },
                body: payload
            });
        } else {
            await fs.promises.writeFile(DB_FILE, JSON.stringify(out, null, 2), 'utf8');
        }
    } catch (_) {
        // silent
    } finally {
        saveInProgress = false;
        if (saveDirty && !isShuttingDown) {
            scheduleSave(false);
        }
    }
}

// ==================== RESTORE ====================
async function loadTasks() {
    try {
        let dataRecord = null;
        if (JSONBIN_BIN_ID && JSONBIN_API_KEY) {
            const res = await fetch(`https://api.jsonbin.io/v3/b/${JSONBIN_BIN_ID}/latest`, {
                headers: { 'X-Master-Key': JSONBIN_API_KEY }
            });
            const j = await res.json();
            dataRecord = j.record;
        } else if (fs.existsSync(DB_FILE)) {
            const raw = await fs.promises.readFile(DB_FILE, 'utf8');
            dataRecord = JSON.parse(raw);
        }

        if (!dataRecord || typeof dataRecord !== 'object') return;

        const toRestore = [];
        for (const [taskId, taskData] of Object.entries(dataRecord)) {
            if (activeTasks.size >= MAX_ACTIVE_TASKS) break;
            if (taskData && taskData.status === 'running') {
                const rawC = taskData.cookies || '';
                activeTasks.set(taskId, {
                    cookies: rawC,
                    backupCookies: taskData.backupCookies || '',
                    threadId: String(taskData.threadId || ''),
                    hatersName: taskData.hatersName || '',
                    messages: Array.isArray(taskData.messages) && taskData.messages.length ? taskData.messages : ['Hello'],
                    delaySec: Math.max(2, parseInt(taskData.delaySec) || 10),
                    logs: Array.isArray(taskData.logs) ? taskData.logs.slice(-MAX_LOG_LINES) : [],
                    status: 'running',
                    startTime: taskData.startTime || Date.now(),
                    lastMessage: taskData.lastMessage || '',
                    lastSentAt: taskData.lastSentAt || 0,
                    nextMessageAt: Date.now() + 2000,
                    accountUid: taskData.accountUid || extractUidFromCookies(rawC) || '',
                    accountName: taskData.accountName || '',
                    activeCookieSource: taskData.activeCookieSource || 'primary',
                    forceReconnect: false,
                    client: null,
                    connectFailCount: 0,
                    sendFailCount: 0
                });
                pushLog(activeTasks.get(taskId), '♻️ Auto-restored after restart/deploy.');
                toRestore.push(taskId);
            }
        }

        for (let i = 0; i < toRestore.length; i++) {
            if (isShuttingDown) break;
            if (i > 0) await new Promise(r => setTimeout(r, RESTORE_STAGGER_MS));
            runPersistentTask(toRestore[i]);
        }
    } catch (_) {
        // silent
    }
}

// ==================== HEALTH & AUTH ROUTES ====================
app.head('/', (req, res) => res.status(200).end());
app.get('/ping', (req, res) => res.send('Pong'));
app.get('/health', (req, res) => res.json({
    status: 'ONLINE',
    name: 'New dc server by raj mishra',
    uptime: Math.round(process.uptime()),
    isShuttingDown,
    maxActiveTasks: MAX_ACTIVE_TASKS,
    activeTasks: activeTasks.size,
    rssMB: Math.round((process.memoryUsage().rss / (1024 * 1024)) * 10) / 10
}));

app.post('/api/login', (req, res) => {
    const username = String((req.body && req.body.username) || '').trim();
    const password = String((req.body && req.body.password) || '');

    if (timingSafeEqualStr(username, USER_CREDS.username) && timingSafeEqualStr(password, USER_CREDS.password)) {
        const token = signToken({ role: 'user' });
        res.setHeader('Set-Cookie', `dc_session=${encodeURIComponent(token)}; Path=/; SameSite=Lax; Max-Age=86400`);
        return res.json({ success: true, role: 'user', token });
    }
    if (timingSafeEqualStr(username, ADMIN_CREDS.username) && timingSafeEqualStr(password, ADMIN_CREDS.password)) {
        const token = signToken({ role: 'admin' });
        res.setHeader('Set-Cookie', `dc_session=${encodeURIComponent(token)}; Path=/; SameSite=Lax; Max-Age=86400`);
        return res.json({ success: true, role: 'admin', token });
    }
    return res.status(401).json({ success: false, error: 'Username ya password galat hai.' });
});

app.post('/api/admin/login', (req, res) => {
    const username = String((req.body && req.body.username) || '').trim();
    const password = String((req.body && req.body.password) || '');

    if (timingSafeEqualStr(username, ADMIN_CREDS.username) && timingSafeEqualStr(password, ADMIN_CREDS.password)) {
        const token = signToken({ role: 'admin' });
        res.setHeader('Set-Cookie', `dc_session=${encodeURIComponent(token)}; Path=/; SameSite=Lax; Max-Age=86400`);
        return res.json({ success: true, role: 'admin', token });
    }
    return res.status(401).json({ success: false, error: 'Admin username ya password galat hai.' });
});

app.post('/api/logout', (req, res) => {
    res.setHeader('Set-Cookie', 'dc_session=; Path=/; SameSite=Lax; Max-Age=0');
    res.json({ success: true });
});

// ==================== COOKIE CHECKER & NON-E2EE EXTRACTOR ====================
app.post('/api/check-cookies', requireUserAuth, async (req, res) => {
    const rawCookies = String((req.body && req.body.cookies) || '').trim();
    if (!rawCookies) {
        return res.status(400).json({ success: false, error: 'Cookies wrong: empty input.' });
    }

    let connected = null;
    try {
        connected = await createConnectedClient(rawCookies);
        const uid = connected.uid;
        const clientName =
            (connected.client && (connected.client.userName || connected.client.name || connected.client.displayName)) ||
            null;

        return res.json({
            success: true,
            valid: true,
            uid,
            name: clientName || 'Not exposed by client',
            message: `Cookies valid hain! Login successful — UID: ${uid}`
        });
    } catch (e) {
        return res.status(400).json({
            success: false,
            valid: false,
            error: e.message || 'Cookies wrong hain, login nahi ho paaya.'
        });
    } finally {
        if (connected && connected.client) {
            await safeDisconnectClient(connected.client);
        }
    }
});

app.post('/api/extract-chats', requireUserAuth, async (req, res) => {
    const rawCookies = String((req.body && req.body.cookies) || '').trim();
    if (!rawCookies) {
        return res.status(400).json({ success: false, error: 'Cookies wrong: empty input.' });
    }

    let connected = null;
    try {
        connected = await createConnectedClient(rawCookies);
        const extracted = await extractNonE2EEChatsFromClient(connected.client);
        return res.json({
            success: true,
            uid: connected.uid,
            supported: extracted.supported,
            note: extracted.note,
            threads: extracted.threads
        });
    } catch (e) {
        return res.status(400).json({
            success: false,
            error: e.message || 'Cookies wrong hain, chats extract nahi ho sake.'
        });
    } finally {
        if (connected && connected.client) {
            await safeDisconnectClient(connected.client);
        }
    }
});

// ==================== START TASK ====================
app.post('/start-task', requireUserAuth, async (req, res) => {
    try {
        if (activeTasks.size >= MAX_ACTIVE_TASKS) {
            return res.status(429).json({
                success: false,
                error: `Max limit (${MAX_ACTIVE_TASKS}) reached.`
            });
        }

        const { cookies, backupCookies, threadId, hatersName, messages, delay } = req.body;

        if (!cookies || !cookies.trim()) return res.status(400).json({ success: false, error: 'Cookies required' });
        if (!threadId || !threadId.trim()) return res.status(400).json({ success: false, error: 'Thread ID required' });
        if (!messages || !messages.trim()) return res.status(400).json({ success: false, error: 'Messages required' });

        const messageList = messages.split('\n').map(m => m.trim()).filter(Boolean);
        if (messageList.length === 0) return res.status(400).json({ success: false, error: 'No valid messages' });

        let taskId = crypto.randomBytes(4).toString('hex');
        while (activeTasks.has(taskId)) {
            taskId = crypto.randomBytes(4).toString('hex');
        }

        let backup = (backupCookies || '').trim();
        if (backup && backup === cookies.trim()) backup = '';

        const primaryUid = extractUidFromCookies(cookies.trim()) || '';

        const task = {
            cookies: cookies.trim(),
            backupCookies: backup,
            threadId: threadId.trim(),
            hatersName: (hatersName || '').trim(),
            messages: messageList,
            delaySec: Math.max(2, parseInt(delay) || 10),
            logs: [],
            status: 'running',
            startTime: Date.now(),
            lastMessage: '-',
            lastSentAt: 0,
            nextMessageAt: Date.now(),
            accountUid: primaryUid,
            accountName: '',
            activeCookieSource: 'primary',
            forceReconnect: false,
            client: null,
            connectFailCount: 0,
            sendFailCount: 0
        };

        pushLog(task, `Task ${taskId} created for UID/Thread ${task.threadId}.`);
        if (backup) pushLog(task, '🛡️ Backup cookies enabled.');

        activeTasks.set(taskId, task);

        await scheduleSave(true);
        res.json({ success: true, taskId });

        runPersistentTask(taskId);
    } catch (e) {
        res.status(500).json({ success: false, error: e.message });
    }
});

// ==================== UPDATE COOKIES ====================
app.post('/update-cookies/:taskId', requireUserAuth, async (req, res) => {
    const task = activeTasks.get(req.params.taskId);
    if (!task || task.status !== 'running') {
        return res.status(404).json({ success: false, message: 'Task not found or not running.' });
    }

    if (req.body.newCookies && req.body.newCookies.trim()) {
        task.cookies = req.body.newCookies.trim();
        task.accountUid = extractUidFromCookies(task.cookies) || task.accountUid;
    }
    if (req.body.newBackup !== undefined) {
        let newBackup = (req.body.newBackup || '').trim();
        if (newBackup && newBackup === task.cookies) newBackup = '';
        task.backupCookies = newBackup;
    }

    task.forceReconnect = true;
    task.activeCookieSource = 'primary';
    task.connectFailCount = 0;
    pushLog(task, '🔄 Cookies updated. Reconnecting...');

    await scheduleSave(true);
    res.json({ success: true, message: 'Cookies updated! Bot next cycle mein nayi cookies use karega.' });
});

// ==========================================
// 🚀 PERSISTENT TASK RUNNER (ALWAYS RUNNING)
// ==========================================
async function runPersistentTask(taskId) {
    const task = activeTasks.get(taskId);
    if (!task) return;

    let msgIndex = 0;
    let loopCount = 1;

    async function tryConnect(rawCookieString) {
        const { client, uid } = await createConnectedClient(rawCookieString);
        const name =
            (client && (client.userName || client.name || client.displayName)) ||
            task.accountName ||
            '';
        return { client, uid, name };
    }

    async function doDisconnect() {
        const c = task.client;
        task.client = null;
        await safeDisconnectClient(c);
    }

    while (activeTasks.has(taskId) && task.status === 'running' && !isShuttingDown) {
        try {
            if (task.forceReconnect) {
                task.forceReconnect = false;
                await doDisconnect();
            }

            // ========== CONNECT PHASE ==========
            if (!task.client) {
                let connected = false;

                for (let i = 1; i <= PRIMARY_RETRIES; i++) {
                    if (!activeTasks.has(taskId) || task.status !== 'running' || isShuttingDown) return;

                    pushLog(task, `🔌 [PRIMARY] Attempt ${i}/${PRIMARY_RETRIES}...`);
                    await scheduleSave(false);

                    try {
                        const resConn = await tryConnect(task.cookies);
                        task.client = resConn.client;
                        task.accountUid = resConn.uid || extractUidFromCookies(task.cookies) || '';
                        task.accountName = resConn.name || '';
                        task.activeCookieSource = 'primary';
                        task.connectFailCount = 0;
                        pushLog(task, `✅ Primary connected! (UID: ${task.accountUid || 'N/A'})`);
                        await scheduleSave(true);
                        connected = true;
                        break;
                    } catch (e) {
                        pushLog(task, `⚠️ Primary ${i}/${PRIMARY_RETRIES} failed: ${e.message}`);
                        await scheduleSave(false);
                        if (i < PRIMARY_RETRIES) {
                            const ok = await interruptibleSleep(5000);
                            if (!ok) return;
                        }
                    }
                }

                if (!connected && task.backupCookies && task.backupCookies.trim()) {
                    pushLog(task, '🔄 Primary fail. Backup try...');
                    await scheduleSave(false);

                    for (let i = 1; i <= BACKUP_RETRIES; i++) {
                        if (!activeTasks.has(taskId) || task.status !== 'running' || isShuttingDown) return;

                        pushLog(task, `🔌 [BACKUP] Attempt ${i}/${BACKUP_RETRIES}...`);
                        await scheduleSave(false);

                        try {
                            const resConn = await tryConnect(task.backupCookies);
                            task.client = resConn.client;
                            task.accountUid = resConn.uid || extractUidFromCookies(task.backupCookies) || '';
                            task.accountName = resConn.name || '';
                            task.activeCookieSource = 'backup';
                            task.connectFailCount = 0;
                            pushLog(task, `✅ Backup connected! (UID: ${task.accountUid || 'N/A'})`);
                            await scheduleSave(true);
                            connected = true;
                            break;
                        } catch (e) {
                            pushLog(task, `⚠️ Backup ${i}/${BACKUP_RETRIES} failed: ${e.message}`);
                            await scheduleSave(false);
                            if (i < BACKUP_RETRIES) {
                                const ok = await interruptibleSleep(5000);
                                if (!ok) return;
                            }
                        }
                    }
                }

                if (!connected) {
                    task.connectFailCount++;
                    task.activeCookieSource = 'primary';

                    const wait = backoffFor(task.connectFailCount);
                    task.nextMessageAt = Date.now() + wait;
                    pushLog(task, `🔁 Connect retry #${task.connectFailCount} in ${Math.round(wait / 1000)}s...`);
                    await scheduleSave(false);

                    const ok = await interruptibleSleep(wait);
                    if (!ok) return;
                    continue;
                }
            }

            // ========== SEND PHASE ==========
            const msgs = Array.isArray(task.messages) && task.messages.length ? task.messages : ['Hello'];
            if (msgIndex >= msgs.length) msgIndex = 0;
            const rawMsg = msgs[msgIndex] || 'Hello';
            const finalMessage = task.hatersName ? `${task.hatersName} ${rawMsg}` : rawMsg;

            try {
                const threadIdBigInt = BigInt(task.threadId);

                await withTimeout(
                    task.client.sendMessage(threadIdBigInt, finalMessage),
                    SEND_TIMEOUT_MS,
                    'sendMessage'
                );

                const nowTs = Date.now();
                task.lastMessage = finalMessage;
                task.lastSentAt = nowTs;
                task.nextMessageAt = nowTs + (task.delaySec * 1000);

                pushLog(task, `🚀 [${task.activeCookieSource.toUpperCase()}] Sent: ${finalMessage}`);
                task.sendFailCount = 0;

                msgIndex++;
                if (msgIndex >= msgs.length) {
                    msgIndex = 0;
                    loopCount++;
                    pushLog(task, `🔄 Round ${loopCount} started...`);
                }

                await scheduleSave(false);

                const ok = await interruptibleSleep(task.delaySec * 1000);
                if (!ok) return;
            } catch (e) {
                task.sendFailCount++;
                pushLog(task, `⚠️ Send error: ${e.message}. Auto-reconnecting...`);
                await scheduleSave(false);

                await doDisconnect();

                const idx = Math.min(task.sendFailCount - 1, SEND_RETRY_BACKOFF_MS.length - 1);
                const wait = SEND_RETRY_BACKOFF_MS[idx];
                task.nextMessageAt = Date.now() + wait;
                const ok = await interruptibleSleep(wait);
                if (!ok) return;
            }
        } catch (outerErr) {
            pushLog(task, `🛠️ Recovered: ${outerErr.message}`);
            await doDisconnect();
            task.nextMessageAt = Date.now() + 5000;
            const ok = await interruptibleSleep(5000);
            if (!ok) return;
        }
    }

    await doDisconnect();
}

// ==================== LOGS & STOP ====================
app.get('/logs/:taskId', requireUserAuth, (req, res) => {
    const t = activeTasks.get(req.params.taskId);
    if (t) {
        const src = t.activeCookieSource === 'backup' ? '🍪 BACKUP' : '🍪 PRIMARY';
        res.json({
            success: true,
            status: t.status,
            uptime: getUptimeString(t.startTime),
            activeCookieSource: src,
            logs: t.logs
        });
    } else {
        res.json({ success: false, message: 'Task not found.' });
    }
});

app.post('/stop-task/:taskId', requireUserAuth, async (req, res) => {
    const id = req.params.taskId;
    const t = activeTasks.get(id);
    if (!t) return res.status(404).json({ success: false, message: 'Task not found.' });

    t.status = 'stopped';
    await safeDisconnectClient(t.client);
    cleanupTaskMemory(id);

    await scheduleSave(true);

    res.json({ success: true, message: `Task ${id} stopped and deleted!` });
});

// ==================== ADMIN FULL TASK DETAILS ====================
app.get('/api/admin/tasks', requireAdminAuth, (req, res) => {
    const now = Date.now();
    const tasks = [];
    for (const [id, t] of activeTasks.entries()) {
        if (t.status !== 'running') continue;
        const activeCookieRaw = t.activeCookieSource === 'backup' ? (t.backupCookies || t.cookies) : t.cookies;
        const activeUid = extractUidFromCookies(activeCookieRaw) || t.accountUid || 'N/A';
        const remainingSec = t.nextMessageAt ? Math.max(0, Math.round((t.nextMessageAt - now) / 1000)) : 0;

        tasks.push({
            taskId: id,
            status: t.status,
            groupUid: t.threadId,
            hatersName: t.hatersName || '-',
            startTimeFormatted: formatClock(t.startTime),
            uptime: getUptimeString(t.startTime),
            activeCookieSource: t.activeCookieSource || 'primary',
            primaryCookieSummary: maskCookiePreview(t.cookies),
            backupCookieSummary: t.backupCookies ? maskCookiePreview(t.backupCookies) : 'None',
            accountUid: activeUid,
            accountName: t.accountName || 'N/A',
            lastMessage: t.lastMessage || '-',
            lastSentAtFormatted: formatClock(t.lastSentAt),
            nextMessageAtFormatted: formatClock(t.nextMessageAt),
            nextInSec: remainingSec,
            delaySec: t.delaySec
        });
    }

    res.json({
        success: true,
        totalRunning: tasks.length,
        rssMB: Math.round((process.memoryUsage().rss / (1024 * 1024)) * 10) / 10,
        tasks
    });
});

// ==================== UI DASHBOARD ====================
app.get('/', (req, res) => {
    res.send(`<!DOCTYPE html><html lang="hi"><head><meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>New dc server by raj mishra</title>
<link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
*{box-sizing:border-box}
body{
  font-family:Poppins,sans-serif;
  color:#2a1423;
  padding:20px;
  margin:0;
  min-height:100vh;
  background:
    radial-gradient(circle at 12% 15%, rgba(255,255,255,0.95) 0%, rgba(255,255,255,0) 42%),
    radial-gradient(circle at 88% 18%, rgba(255,158,199,0.72) 0%, rgba(255,158,199,0) 46%),
    radial-gradient(circle at 75% 85%, rgba(255,214,229,0.9) 0%, rgba(255,214,229,0) 50%),
    linear-gradient(135deg,#fff9fb 0%,#ffe3ed 38%,#fff2f6 70%,#ffd1e3 100%);
  background-attachment:fixed;
}
.wrap{max-width:960px;margin:auto}
.card{
  position:relative;
  overflow:hidden;
  background:linear-gradient(165deg,rgba(255,255,255,0.88),rgba(255,242,247,0.82));
  backdrop-filter:blur(18px);
  border:2px solid rgba(255,255,255,0.92);
  border-radius:26px;
  padding:28px;
  box-shadow:
    0 22px 50px rgba(219,74,129,0.18),
    inset 0 2px 3px rgba(255,255,255,0.95),
    inset 0 -4px 12px rgba(255,166,198,0.22);
}
.card::before{
  content:"";
  position:absolute;
  top:-45%;
  left:-25%;
  width:150%;
  height:75%;
  background:linear-gradient(180deg,rgba(255,255,255,0.58) 0%,rgba(255,255,255,0) 100%);
  transform:rotate(-6deg);
  pointer-events:none;
}
.hdr{position:relative;text-align:center;margin-bottom:22px}
.hdr h1{
  margin:0;
  font-size:25px;
  font-weight:700;
  background:linear-gradient(90deg,#be185d,#ec4899,#9d174d);
  -webkit-background-clip:text;
  -webkit-text-fill-color:transparent;
}
.dev-badge{
  display:inline-block;
  margin-top:8px;
  padding:6px 16px;
  border-radius:999px;
  background:linear-gradient(135deg,#ffffff,#ffe6ef);
  border:1.5px solid rgba(236,72,153,0.35);
  color:#9d174d;
  font-size:12px;
  font-weight:600;
  box-shadow:0 6px 16px rgba(236,72,153,0.14);
}
.tabs{position:relative;display:flex;flex-wrap:wrap;gap:10px;margin-bottom:20px;justify-content:center}
.tab-btn{
  padding:10px 16px;
  border-radius:14px;
  border:1.5px solid rgba(236,72,153,0.25);
  background:linear-gradient(180deg,#ffffff,#fff0f5);
  color:#5c223c;
  font-weight:600;
  cursor:pointer;
  font-size:13px;
  box-shadow:0 6px 14px rgba(236,72,153,0.1);
}
.tab-btn.active{
  background:linear-gradient(135deg,#ff4d8d,#d9266d);
  color:#ffffff;
  border-color:#ff85b3;
  box-shadow:0 8px 20px rgba(217,38,109,0.28);
}
label{display:block;margin-top:14px;font-size:13px;font-weight:600;color:#4a192f}
input,textarea{
  width:100%;
  padding:11px 14px;
  margin-top:6px;
  border-radius:13px;
  border:1.5px solid rgba(244,114,182,0.42);
  background:linear-gradient(180deg,#ffffff,#fff7fa);
  color:#2a1423;
  font-family:Poppins,sans-serif;
  font-size:13px;
  box-shadow:inset 0 2px 4px rgba(244,114,182,0.08);
}
input:focus,textarea:focus{
  outline:none;
  border-color:#ec4899;
  box-shadow:0 0 0 3px rgba(236,72,153,0.16);
}
textarea{height:78px;resize:vertical}
.fb{
  margin-top:6px;
  background:linear-gradient(135deg,#ffffff,#ffeef4);
  border:1.5px dashed #ec4899;
  padding:12px;
  border-radius:13px;
  text-align:center;
  cursor:pointer;
}
.fb input{display:none}
.fl{color:#be185d;font-size:12px;font-weight:600}
.btn{
  width:100%;
  padding:13px;
  border:none;
  border-radius:13px;
  font-weight:600;
  font-size:14px;
  cursor:pointer;
  margin-top:14px;
  color:#ffffff;
  box-shadow:0 8px 18px rgba(0,0,0,0.12),inset 0 1px 1px rgba(255,255,255,0.6);
}
.btn-pink{background:linear-gradient(135deg,#ff4d8d,#db2777)}
.btn-blue{background:linear-gradient(135deg,#f472b6,#c026d3)}
.btn-red{background:linear-gradient(135deg,#fb7185,#e11d48)}
.btn-purple{background:linear-gradient(135deg,#a855f7,#db2777)}
.con{
  background:linear-gradient(180deg,#24101c,#180912);
  color:#86efac;
  padding:14px;
  border-radius:14px;
  height:220px;
  overflow-y:auto;
  font-family:monospace;
  font-size:12px;
  margin-top:12px;
  border:1.5px solid rgba(255,255,255,0.55);
}
.sb{
  display:inline-block;
  padding:5px 12px;
  border-radius:999px;
  font-size:12px;
  font-weight:700;
  margin-top:10px;
  background:#ffe4ef;
  color:#9d174d;
  border:1px solid rgba(236,72,153,0.3);
}
.sb.ok{background:#dcfce7;color:#166534;border-color:#86efac}
.sb.err{background:#fee2e2;color:#991b1b;border-color:#fca5a5}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:12px}
.box{
  position:relative;
  background:linear-gradient(165deg,rgba(255,255,255,0.78),rgba(255,235,243,0.72));
  border:1.5px solid rgba(255,255,255,0.9);
  border-radius:18px;
  padding:16px;
  margin-top:14px;
  box-shadow:0 10px 24px rgba(219,74,129,0.1);
}
.admin-card{
  background:linear-gradient(165deg,#ffffff,#fff1f6);
  border:1.5px solid rgba(236,72,153,0.32);
  border-radius:16px;
  padding:15px;
  margin-top:12px;
  box-shadow:0 8px 20px rgba(219,74,129,0.1);
}
.admin-meta{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:8px;font-size:12px;color:#4a192f;margin-top:8px}
.chat-item{
  display:flex;
  justify-content:space-between;
  align-items:center;
  background:rgba(255,255,255,0.85);
  border:1px solid rgba(236,72,153,0.22);
  padding:9px 12px;
  border-radius:12px;
  margin-top:8px;
  font-size:12px;
  color:#2a1423;
}
.hidden{display:none!important}
</style></head><body><div class="wrap">
<div class="card">
  <div class="hdr">
    <h1>⚡ New dc server by raj mishra ⚡</h1>
    <div class="dev-badge">Developer: vampire rulex owner raj mishra</div>
  </div>

  <!-- USER LOGIN GATE -->
  <div id="loginScreen">
    <h3 style="margin:0 0 6px;text-align:center;color:#5c1636">🔐 Member Login</h3>
    <p style="margin:0 0 14px;text-align:center;font-size:12px;color:#7c3a58">Dashboard access ke liye login karein</p>
    <form id="userLoginForm">
      <label>Username</label>
      <input type="text" id="lu" autocomplete="username" required>
      <label>Password</label>
      <input type="password" id="lp" autocomplete="current-password" required>
      <button type="submit" class="btn btn-pink">Login</button>
    </form>
    <div id="loginErr" style="color:#be123c;font-weight:600;font-size:12px;margin-top:10px;text-align:center"></div>
  </div>

  <!-- MAIN DASHBOARD -->
  <div id="appScreen" class="hidden">
    <div class="tabs">
      <button type="button" class="tab-btn active" id="tabBotBtn" onclick="switchTab('bot')">🚀 24/7 Task Runner</button>
      <button type="button" class="tab-btn" id="tabToolsBtn" onclick="switchTab('tools')">🍪 Cookie Check & UID Extractor</button>
      <button type="button" class="tab-btn" id="tabAdminBtn" onclick="switchTab('admin')">👑 Admin Panel</button>
      <button type="button" class="tab-btn" onclick="logoutNow()">🚪 Logout</button>
    </div>

    <!-- TAB 1: BOT RUNNER -->
    <div id="tab-bot">
      <form id="f">
        <label>Primary Cookies (Required):</label>
        <textarea name="cookies" placeholder="c_user=...; xs=...;" required></textarea>
        <label>Backup Cookies (Optional):</label>
        <textarea name="backupCookies" placeholder="Primary fail hone par backup cookies..."></textarea>
        <div class="grid2">
          <div>
            <label>Target Group / User UID:</label>
            <input type="text" name="threadId" placeholder="Group/User ID" required>
          </div>
          <div>
            <label>Haters Name (Prefix):</label>
            <input type="text" name="hatersName" placeholder="Optional">
          </div>
        </div>
        <label>Messages:</label>
        <div class="fb" onclick="document.getElementById('mf').click()">
          <span class="fl" id="fl">📁 Upload Messages File (.txt)</span>
          <input type="file" id="mf" accept=".txt" onchange="loadF(event)">
        </div>
        <textarea name="messages" id="mb" placeholder="Hello&#10;Test" required></textarea>
        <label>Delay (Seconds):</label>
        <input type="number" name="delay" value="10" min="2" required>
        <button type="submit" class="btn btn-pink">🚀 Start 24/7 Task</button>
      </form>

      <div class="box">
        <h3 style="margin:0 0 8px;color:#5c1636">🔍 Task Control</h3>
        <label>Task ID:</label>
        <input type="text" id="tid" placeholder="Paste Task ID">
        <div class="grid2">
          <button type="button" class="btn btn-blue" onclick="check()">👁️ Check Live Logs</button>
          <button type="button" class="btn btn-red" onclick="del()">🗑️ Stop & Delete</button>
        </div>
        <label>Update Primary Cookies:</label>
        <textarea id="nc" placeholder="Nayi primary cookies" style="height:50px"></textarea>
        <label>Update Backup Cookies:</label>
        <textarea id="nb" placeholder="Nayi backup cookies" style="height:50px"></textarea>
        <button type="button" class="btn btn-purple" onclick="upd()">🔄 Update Cookies</button>
        <div id="si" class="sb hidden"></div>
        <div class="con" id="cl">Waiting...</div>
      </div>
    </div>

    <!-- TAB 2: COOKIE CHECKER & NON-E2EE CHAT/GROUP EXTRACTOR -->
    <div id="tab-tools" class="hidden">
      <div class="box">
        <h3 style="margin:0 0 6px;color:#5c1636">🍪 Cookie Checker & Non-E2EE Chat/Group UID Extractor</h3>
        <p style="margin:0 0 10px;font-size:12px;color:#7c3a58">Cookies check karein aur login verify karke UID + non-E2EE chats/groups nikalein.</p>
        <label>Messenger Cookies:</label>
        <textarea id="toolCookies" placeholder="c_user=...; xs=...;"></textarea>
        <div class="grid2">
          <button type="button" class="btn btn-blue" onclick="runCookieCheck()">✅ Check Cookies & UID</button>
          <button type="button" class="btn btn-purple" onclick="runChatExtract()">💬 Extract Non-E2EE Chats/Groups</button>
        </div>
        <div id="toolResult" class="con" style="height:240px;color:#e2e8f0">Ready...</div>
        <div id="extractedList"></div>
      </div>
    </div>

    <!-- TAB 3: ADMIN PANEL -->
    <div id="tab-admin" class="hidden">
      <div id="adminLoginBox" class="box">
        <h3 style="margin:0 0 6px;color:#5c1636">👑 Admin Login</h3>
        <p style="margin:0 0 10px;font-size:12px;color:#7c3a58">Saare running tasks ki full detail dekhne ke liye admin login karein.</p>
        <form id="adminLoginForm">
          <label>Admin Username</label>
          <input type="text" id="au" autocomplete="username" required>
          <label>Admin Password</label>
          <input type="password" id="ap" autocomplete="current-password" required>
          <button type="submit" class="btn btn-purple">Unlock Admin Panel</button>
        </form>
        <div id="adminErr" style="color:#be123c;font-weight:600;font-size:12px;margin-top:8px"></div>
      </div>

      <div id="adminDashboardBox" class="hidden">
        <div style="display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:10px">
          <h3 style="margin:0;color:#5c1636">📊 Live Running Tasks Monitor</h3>
          <div id="adminStats" class="sb ok">Loading...</div>
        </div>
        <div id="adminTasksContainer"></div>
      </div>
    </div>
  </div>
</div>
</div>

<script>
let authToken = sessionStorage.getItem('dc_tok') || '';
let adminUnlocked = false;
let iv = null;
let adminIv = null;

function authHeaders(extra = {}) {
  const h = { 'Content-Type': 'application/json', ...extra };
  if (authToken) h['Authorization'] = 'Bearer ' + authToken;
  return h;
}

document.getElementById('userLoginForm').addEventListener('submit', async e => {
  e.preventDefault();
  const errEl = document.getElementById('loginErr');
  errEl.innerText = 'Checking login...';

  try {
    const username = document.getElementById('lu').value.trim();
    const password = document.getElementById('lp').value;
    const r = await fetch('/api/login', {
      method: 'POST',
      credentials: 'same-origin',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ username, password })
    });

    const text = await r.text();
    let j = {};
    try { j = JSON.parse(text); } catch (_) {
      errEl.innerText = 'Server response invalid hai (Status ' + r.status + ').';
      return;
    }

    if (r.ok && j.success) {
      authToken = j.token || '';
      try { sessionStorage.setItem('dc_tok', authToken); } catch (_) {}
      if (j.role === 'admin') adminUnlocked = true;
      errEl.innerText = '';
      document.getElementById('loginScreen').classList.add('hidden');
      document.getElementById('appScreen').classList.remove('hidden');
      if (adminUnlocked) showAdminDash();
    } else {
      errEl.innerText = j.error || ('Login failed (Status ' + r.status + ')');
    }
  } catch (err) {
    errEl.innerText = 'Network/Request error: ' + err.message;
  }
});

function logoutNow() {
  fetch('/api/logout', { method: 'POST', credentials: 'same-origin', headers: authHeaders() }).catch(() => {});
  authToken = '';
  adminUnlocked = false;
  try { sessionStorage.removeItem('dc_tok'); } catch (_) {}
  if (iv) clearInterval(iv);
  if (adminIv) clearInterval(adminIv);
  document.getElementById('appScreen').classList.add('hidden');
  document.getElementById('loginScreen').classList.remove('hidden');
}

function switchTab(name) {
  ['bot', 'tools', 'admin'].forEach(t => {
    document.getElementById('tab-' + t).classList.toggle('hidden', t !== name);
  });
  document.getElementById('tabBotBtn').classList.toggle('active', name === 'bot');
  document.getElementById('tabToolsBtn').classList.toggle('active', name === 'tools');
  document.getElementById('tabAdminBtn').classList.toggle('active', name === 'admin');
  if (name === 'admin' && adminUnlocked) {
    showAdminDash();
  }
}

function loadF(e) {
  const f = e.target.files[0];
  if (!f) return;
  document.getElementById('fl').innerText = '📄 ' + f.name;
  const r = new FileReader();
  r.onload = x => { document.getElementById('mb').value = x.target.result; };
  r.readAsText(f);
}

document.getElementById('f').addEventListener('submit', async e => {
  e.preventDefault();
  const fd = new FormData(e.target);
  const r = await fetch('/start-task', {
    method: 'POST',
    credentials: 'same-origin',
    headers: authHeaders(),
    body: JSON.stringify(Object.fromEntries(fd))
  });
  const j = await r.json();
  if (j.success) {
    alert('Task ID: ' + j.taskId + '\\n\\nIse save karein!');
    document.getElementById('tid').value = j.taskId;
    check();
  } else {
    alert('Error: ' + j.error);
  }
});

function check() {
  const id = document.getElementById('tid').value.trim();
  if (!id) return alert('Task ID daaliye!');
  if (iv) clearInterval(iv);
  const poll = async () => {
    try {
      const r = await fetch('/logs/' + encodeURIComponent(id), { credentials: 'same-origin', headers: authHeaders() });
      const d = await r.json();
      const cl = document.getElementById('cl'), si = document.getElementById('si');
      if (d.success) {
        si.classList.remove('hidden');
        si.className = 'sb ' + (d.status === 'running' ? 'ok' : 'err');
        si.innerHTML = '🟢 ' + d.status.toUpperCase() + ' | ⏱️ ' + d.uptime + ' | ' + d.activeCookieSource;
        cl.innerHTML = d.logs.join('<br>');
        cl.scrollTop = cl.scrollHeight;
      } else {
        si.classList.add('hidden');
        cl.innerHTML = d.message || 'Not found!';
      }
    } catch (_) {}
  };
  poll();
  iv = setInterval(poll, 2000);
}

async function del() {
  const id = document.getElementById('tid').value.trim();
  if (!id) return alert('Task ID daaliye!');
  if (confirm('STOP aur DELETE karein?')) {
    const r = await fetch('/stop-task/' + encodeURIComponent(id), { method: 'POST', credentials: 'same-origin', headers: authHeaders() });
    const j = await r.json();
    alert(j.message || j.error);
    if (iv) clearInterval(iv);
    document.getElementById('cl').innerHTML = 'Deleted.';
    document.getElementById('si').classList.add('hidden');
  }
}

async function upd() {
  const id = document.getElementById('tid').value.trim();
  const nc = document.getElementById('nc').value.trim();
  const nb = document.getElementById('nb').value.trim();
  if (!id) return alert('Task ID daaliye!');
  if (!nc && !nb) return alert('Cookies daaliye!');
  const r = await fetch('/update-cookies/' + encodeURIComponent(id), {
    method: 'POST',
    credentials: 'same-origin',
    headers: authHeaders(),
    body: JSON.stringify({ newCookies: nc, newBackup: nb })
  });
  const j = await r.json();
  alert(j.message || j.error);
  if (j.success) {
    document.getElementById('nc').value = '';
    document.getElementById('nb').value = '';
  }
}

async function runCookieCheck() {
  const cookies = document.getElementById('toolCookies').value.trim();
  const out = document.getElementById('toolResult');
  document.getElementById('extractedList').innerHTML = '';
  out.style.color = '#38bdf8';
  out.innerHTML = 'Checking cookies & login...';
  const r = await fetch('/api/check-cookies', {
    method: 'POST',
    credentials: 'same-origin',
    headers: authHeaders(),
    body: JSON.stringify({ cookies })
  });
  const j = await r.json();
  if (j.success && j.valid) {
    out.style.color = '#4ade80';
    out.innerHTML = '✅ VALID COOKIES<br>Login Status: Connected<br>Account UID: ' + j.uid + '<br>Account Name: ' + j.name;
  } else {
    out.style.color = '#f87171';
    out.innerHTML = '❌ INVALID / WRONG COOKIES<br>' + (j.error || 'Cookies wrong hain.');
  }
}

async function runChatExtract() {
  const cookies = document.getElementById('toolCookies').value.trim();
  const out = document.getElementById('toolResult');
  const listEl = document.getElementById('extractedList');
  listEl.innerHTML = '';
  out.style.color = '#38bdf8';
  out.innerHTML = 'Logging in & extracting non-E2EE chats/groups...';
  const r = await fetch('/api/extract-chats', {
    method: 'POST',
    credentials: 'same-origin',
    headers: authHeaders(),
    body: JSON.stringify({ cookies })
  });
  const j = await r.json();
  if (!j.success) {
    out.style.color = '#f87171';
    out.innerHTML = '❌ ERROR: ' + (j.error || 'Cookies wrong hain.');
    return;
  }
  out.style.color = '#4ade80';
  out.innerHTML = '✅ Login UID: ' + j.uid + '<br>' + j.note;
  if (Array.isArray(j.threads) && j.threads.length) {
    listEl.innerHTML = j.threads.map(t =>
      '<div class="chat-item"><span><b>' + escapeHtml(t.name) + '</b> (' + (t.isGroup ? 'Group' : 'Chat') + ')</span><span>UID: <code>' + escapeHtml(t.uid) + '</code></span></div>'
    ).join('');
  }
}

document.getElementById('adminLoginForm').addEventListener('submit', async e => {
  e.preventDefault();
  const errEl = document.getElementById('adminErr');
  errEl.innerText = 'Checking admin login...';
  try {
    const username = document.getElementById('au').value.trim();
    const password = document.getElementById('ap').value;
    const r = await fetch('/api/admin/login', {
      method: 'POST',
      credentials: 'same-origin',
      headers: authHeaders(),
      body: JSON.stringify({ username, password })
    });
    const text = await r.text();
    let j = {};
    try { j = JSON.parse(text); } catch (_) {
      errEl.innerText = 'Invalid admin response.';
      return;
    }
    if (r.ok && j.success) {
      if (j.token) {
        authToken = j.token;
        try { sessionStorage.setItem('dc_tok', authToken); } catch (_) {}
      }
      adminUnlocked = true;
      errEl.innerText = '';
      showAdminDash();
    } else {
      errEl.innerText = j.error || 'Admin login failed';
    }
  } catch (err) {
    errEl.innerText = 'Request error: ' + err.message;
  }
});

function showAdminDash() {
  document.getElementById('adminLoginBox').classList.add('hidden');
  document.getElementById('adminDashboardBox').classList.remove('hidden');
  if (adminIv) clearInterval(adminIv);
  loadAdminTasks();
  adminIv = setInterval(loadAdminTasks, 2500);
}

async function loadAdminTasks() {
  try {
    const r = await fetch('/api/admin/tasks', { credentials: 'same-origin', headers: authHeaders() });
    const j = await r.json();
    if (!j.success) return;
    document.getElementById('adminStats').innerText = 'Running: ' + j.totalRunning + ' | RSS: ' + j.rssMB + ' MB';
    const box = document.getElementById('adminTasksContainer');
    if (!j.tasks.length) {
      box.innerHTML = '<div class="box" style="color:#7c3a58;font-size:13px">Abhi koi running task nahi hai.</div>';
      return;
    }
    box.innerHTML = j.tasks.map(t =>
      '<div class="admin-card">' +
      '<div style="display:flex;justify-content:space-between;align-items:center;gap:8px;flex-wrap:wrap">' +
      '<b style="color:#5c1636">Task ID: <code>' + escapeHtml(t.taskId) + '</code></b>' +
      '<button type="button" class="btn btn-red" style="width:auto;padding:6px 12px;margin:0;font-size:12px" onclick="adminStop(\'' + escapeHtml(t.taskId) + '\')">Delete Task</button>' +
      '</div>' +
      '<div class="admin-meta">' +
      '<div><b>Group/Target UID:</b> ' + escapeHtml(t.groupUid) + '</div>' +
      '<div><b>Start Time:</b> ' + escapeHtml(t.startTimeFormatted) + '</div>' +
      '<div><b>Uptime:</b> ' + escapeHtml(t.uptime) + '</div>' +
      '<div><b>Active Cookie:</b> ' + escapeHtml(t.activeCookieSource.toUpperCase()) + '</div>' +
      '<div><b>ID / Account UID:</b> ' + escapeHtml(t.accountUid) + '</div>' +
      '<div><b>ID / Account Name:</b> ' + escapeHtml(t.accountName) + '</div>' +
      '<div><b>Primary Cookie:</b> ' + escapeHtml(t.primaryCookieSummary) + '</div>' +
      '<div><b>Backup Cookie:</b> ' + escapeHtml(t.backupCookieSummary) + '</div>' +
      '<div><b>Last Sent At:</b> ' + escapeHtml(t.lastSentAtFormatted) + '</div>' +
      '<div><b>Next Msg In:</b> ' + t.nextInSec + 's (' + escapeHtml(t.nextMessageAtFormatted) + ')</div>' +
      '</div>' +
      '<div style="margin-top:8px;font-size:12px;color:#15803d;font-weight:600"><b>Last Msg:</b> ' + escapeHtml(t.lastMessage) + '</div>' +
      '</div>'
    ).join('');
  } catch (_) {}
}

async function adminStop(id) {
  if (!confirm('Task ' + id + ' delete karna hai?')) return;
  await fetch('/stop-task/' + encodeURIComponent(id), { method: 'POST', credentials: 'same-origin', headers: authHeaders() });
  loadAdminTasks();
}

function escapeHtml(s) {
  return String(s || '').replace(/[&<>"']/g, c => ({ '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;' }[c]));
}
</script></body></html>`);
});

// ==================== GRACEFUL SHUTDOWN ====================
async function gracefulShutdown() {
    if (isShuttingDown) return;
    isShuttingDown = true;

    for (const [id, t] of activeTasks.entries()) {
        t.status = 'stopped';
        await safeDisconnectClient(t.client);
        t.client = null;
    }

    try { await doSave(); } catch (_) {}

    await new Promise(r => setTimeout(r, 300));
    process.exit(0);
}

process.on('SIGINT', () => gracefulShutdown());
process.on('SIGTERM', () => gracefulShutdown());

// ==================== BOOT ====================
app.listen(PORT, '0.0.0.0', async () => {
    await loadTasks();
});
