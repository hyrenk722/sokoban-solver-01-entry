// Sokoban solver: room decomposition + push-optimal BFS per room.
// Reads /input/<id>/level.txt, writes /output/<id>/solution.txt (LURD moves).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIRS = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
const CAP = 1500000;

function parse(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

// Squares from which a box alone can be pushed onto some goal (walls only).
function liveSquares(w, wall, goals) {
  const live = new Uint8Array(wall.length);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) { live[y] = 1; queue.push(y); }
    }
  }
  return live;
}

// Flood the player's reachable region into seen[] with `stamp`; return its lowest square.
function reach(w, wall, occ, from, seen, stamp, stack) {
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    const q1 = p - w, q2 = p + w, q3 = p - 1, q4 = p + 1;
    if (!wall[q1] && !occ[q1] && seen[q1] !== stamp) { seen[q1] = stamp; stack[n++] = q1; }
    if (!wall[q2] && !occ[q2] && seen[q2] !== stamp) { seen[q2] = stamp; stack[n++] = q2; }
    if (!wall[q3] && !occ[q3] && seen[q3] !== stamp) { seen[q3] = stamp; stack[n++] = q3; }
    if (!wall[q4] && !occ[q4] && seen[q4] !== stamp) { seen[q4] = stamp; stack[n++] = q4; }
  }
  return low;
}

// A frozen 2x2 of walls/boxes holding a box off its goal, around the box just pushed to t.
function frozen(w, wall, occ, goal, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || occ[a]) || !(wall[b] || occ[b]) || !(wall[c] || occ[c]) || !(wall[d] || occ[d])) continue;
    if ((occ[a] && !goal[a]) || (occ[b] && !goal[b]) || (occ[c] && !goal[c]) || (occ[d] && !goal[d])) return true;
  }
  return false;
}

// Shortest walk from `from` to `to` around walls and boxes, lower-case LURD.
function walkTo(w, wall, occ, from, to) {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occ[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

// Push-optimal BFS. wall/goals/boxes describe the sub-board; player is the player's square.
// Returns {pushes, moves} or null when the state cap is hit or no solution exists.
function solve(w, wall, goals, boxes0, player0, cap, stringKey) {
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(w, wall, goals);
  const occ = new Uint8Array(size);
  const seenA = new Int32Array(size);
  const seenB = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  const solved = (B) => B.every((b) => goal[b]);
  if (boxes0.some((b) => !live[b])) return null;
  const keyOf = stringKey
    ? (B, low) => B.join(',') + '|' + low
    : (B, low) => { let k = low; for (const b of B) k = k * size + b; return k; };
  const SB = [boxes0];
  const SP = [player0];
  const PA = [-1];
  const index = new Map();
  for (const b of boxes0) occ[b] = 1;
  index.set(keyOf(boxes0, reach(w, wall, occ, player0, seenA, ++stamp, stack)), 0);
  for (const b of boxes0) occ[b] = 0;
  let found = solved(boxes0) ? 0 : -1;
  for (let head = 0; found < 0 && head < SB.length; head++) {
    const boxes = SB[head];
    for (const b of boxes) occ[b] = 1;
    reach(w, wall, occ, SP[head], seenA, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (seenA[b - d] !== here || wall[t] || occ[t] || !live[t]) continue;
        occ[b] = 0; occ[t] = 1;
        const froz = frozen(w, wall, occ, goal, t);
        let key = null, next = null;
        if (!froz) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((x, y) => x - y);
          key = keyOf(next, reach(w, wall, occ, b, seenB, ++stamp, stack));
        }
        occ[t] = 0; occ[b] = 1;
        if (froz || index.has(key)) continue;
        if (SB.length >= cap) { for (const x of boxes) occ[x] = 0; return null; }
        index.set(key, SB.length);
        SB.push(next);
        SP.push(b);
        PA.push(head);
        if (solved(next)) { found = SB.length - 1; break; }
      }
    }
    for (const x of boxes) occ[x] = 0;
  }
  if (found < 0) return null;
  const path = [];
  for (let s = found; s > 0; s = PA[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = player0;
  let boxes = boxes0;
  for (const s of path) {
    const nextBoxes = SB[s];
    const from = boxes.find((b) => !nextBoxes.includes(b));
    const to = nextBoxes.find((b) => !boxes.includes(b));
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d);
    for (const b of boxes) occ[b] = 1;
    moves += walkTo(w, wall, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

// Cut the dead squares of the player's row (the hallway) out of the floor; each remaining
// part holding boxes is a room. Null when the level is not a clean set of rooms.
function roomsOf(L) {
  const { w, wall, goals, boxes, player } = L;
  const live = liveSquares(w, wall, goals);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const parts = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = parts.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i] + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = parts.length; squares.push(q); }
      }
    }
    parts.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) parts[part[b]].boxes.push(b);
  for (const g of goals) { if (part[g] < 0) return null; parts[part[g]].goals.push(g); }
  if (parts.some((r) => r.boxes.length !== r.goals.length)) return null;
  return parts.filter((r) => r.boxes.length > 0);
}

function endOf(w, from, moves) {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

function solveLevel(text) {
  const L = parse(text);
  const { w, wall } = L;
  const rooms = roomsOf(L);
  if (rooms === null) {
    const whole = solve(w, wall, L.goals, L.boxes, L.player, 400000, true);
    return whole ? whole.moves : '';
  }
  // Assign each box to its room; track current positions as rooms are solved.
  const roomOfBox = new Map();
  rooms.forEach((r, ri) => r.boxes.forEach((b) => roomOfBox.set(b, ri)));
  const cur = new Map(); // initial cell -> current cell
  for (const b of L.boxes) cur.set(b, b);
  let player = L.player;
  let moves = '';
  for (let ri = 0; ri < rooms.length; ri++) {
    const room = rooms[ri];
    const subWall = wall.slice();
    for (const b of L.boxes) if (roomOfBox.get(b) !== ri) subWall[cur.get(b)] = 1;
    const roomBoxes = room.boxes.map((b) => cur.get(b)).sort((a, b) => a - b);
    const solved = solve(w, subWall, room.goals, roomBoxes, player, CAP, false);
    if (solved === null) {
      const whole = solve(w, wall, L.goals, L.boxes, L.player, 400000, true);
      return whole ? whole.moves : '';
    }
    moves += solved.moves;
    player = endOf(w, player, solved.moves);
    // The room's boxes now stand on its goals (as a set).
    const goalSet = [...room.goals].sort((a, b) => a - b);
    room.boxes.forEach((b, i) => cur.set(b, goalSet[i]));
  }
  return moves;
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
