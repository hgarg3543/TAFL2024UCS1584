const SAMPLES = {
    simple: {
        states: 'q0,q1,q2,q3,q4',
        alpha: 'a,b',
        start: 'q0',
        finals: 'q3,q4',
        trans: `q0,a,q1\nq0,b,q2\nq1,a,q3\nq1,b,q4\nq2,a,q3\nq2,b,q4\nq3,a,q3\nq3,b,q3\nq4,a,q4\nq4,b,q4`
    },
    redundant: {
        states: 'q0,q1,q2,q3,q4,q5',
        alpha: '0,1',
        start: 'q0',
        finals: 'q2,q4',
        trans: `q0,0,q1\nq0,1,q3\nq1,0,q2\nq1,1,q5\nq2,0,q2\nq2,1,q5\nq3,0,q4\nq3,1,q5\nq4,0,q4\nq4,1,q5\nq5,0,q5\nq5,1,q5`
    },
    unreachable: {
        states: 'q0,q1,q2,q3,q4,q5',
        alpha: 'a,b',
        start: 'q0',
        finals: 'q2',
        trans: `q0,a,q1\nq0,b,q0\nq1,a,q2\nq1,b,q0\nq2,a,q2\nq2,b,q2\nq3,a,q4\nq3,b,q5\nq4,a,q3\nq4,b,q5\nq5,a,q5\nq5,b,q5`
    },
    complex: {
        states: 'A,B,C,D,E,F,G',
        alpha: '0,1',
        start: 'A',
        finals: 'C,F',
        trans: `A,0,B\nA,1,D\nB,0,C\nB,1,E\nC,0,C\nC,1,C\nD,0,E\nD,1,F\nE,0,E\nE,1,E\nF,0,F\nF,1,F\nG,0,A\nG,1,B`
    }
};

let dfa = null;
let steps = [];
let currentStep = -1;
let playing = false;
let playTimer = null;

function loadSample(name) {
    const s = SAMPLES[name];
    document.getElementById('inp-states').value = s.states;
    document.getElementById('inp-alpha').value = s.alpha;
    document.getElementById('inp-start').value = s.start;
    document.getElementById('inp-finals').value = s.finals;
    document.getElementById('inp-trans').value = s.trans;
    document.querySelectorAll('.sample-btn').forEach(b => b.classList.toggle('active', b.textContent.toLowerCase() === name));
    buildDFA();
}

function showError(msg) {
    const el = document.getElementById('error-msg');
    el.textContent = msg;
    el.classList.add('show');
}

function hideError() {
    document.getElementById('error-msg').classList.remove('show');
}

function parseDFA() {
    const states = document.getElementById('inp-states').value.split(',').map(s=>s.trim()).filter(Boolean);
    const alpha = document.getElementById('inp-alpha').value.split(',').map(s=>s.trim()).filter(Boolean);
    const start = document.getElementById('inp-start').value.trim();
    const finals = document.getElementById('inp-finals').value.split(',').map(s=>s.trim()).filter(Boolean);
    const transLines = document.getElementById('inp-trans').value.split('\n').map(s=>s.trim()).filter(Boolean);

    if (!states.length) { showError('States cannot be empty'); return null; }
    if (!alpha.length) { showError('Alphabet cannot be empty'); return null; }
    if (!states.includes(start)) { showError(`Start state "${start}" not in states list`); return null; }
    for (const f of finals) {
        if (!states.includes(f)) { showError(`Final state "${f}" not in states list`); return null; }
    }

    const trans = {};
    for (const st of states) { trans[st] = {}; }

    for (const line of transLines) {
        const parts = line.split(',').map(s=>s.trim());
        if (parts.length !== 3) { showError(`Invalid transition: "${line}" — expected state,symbol,next`); return null; }
        const [from, sym, to] = parts;
        if (!states.includes(from)) { showError(`Unknown state in transition: "${from}"`); return null; }
        if (!alpha.includes(sym)) { showError(`Unknown symbol in transition: "${sym}"`); return null; }
        if (!states.includes(to)) { showError(`Unknown state in transition target: "${to}"`); return null; }
        trans[from][sym] = to;
    }

    return { states, alpha, start, finals, trans };
}

function computeReachable(dfa) {
    const visited = new Set([dfa.start]);
    const queue = [dfa.start];
    while (queue.length) {
        const s = queue.shift();
        for (const sym of dfa.alpha) {
            const t = dfa.trans[s]?.[sym];
            if (t && !visited.has(t)) { visited.add(t); queue.push(t); }
        }
    }
    return visited;
}

function hopcroft(states, alpha, finals, trans) {
    const nonFinals = states.filter(s => !finals.includes(s));
    let partitions = [];
    if (finals.length) partitions.push(new Set(finals));
    if (nonFinals.length) partitions.push(new Set(nonFinals));

    const history = [partitions.map(p => new Set(p))];
    const splitHistory = [];

    let changed = true;
    while (changed) {
        changed = false;
        const newPartitions = [];
        for (const group of partitions) {
            const members = [...group];
            if (members.length === 1) { newPartitions.push(group); continue; }

            let splitDone = false;
            for (const sym of alpha) {
                const signature = s => {
                    const target = trans[s]?.[sym];
                    if (!target) return -1;
                    return partitions.findIndex(p => p.has(target));
                };
                const sigs = {};
                for (const s of members) {
                    const sig = signature(s);
                    if (!sigs[sig]) sigs[sig] = [];
                    sigs[sig].push(s);
                }
                const keys = Object.keys(sigs);
                if (keys.length > 1) {
                    for (const k of keys) newPartitions.push(new Set(sigs[k]));
                    splitHistory.push({ group: new Set(group), symbol: sym, splits: keys.map(k => sigs[k]) });
                    changed = true;
                    splitDone = true;
                    break;
                }
            }
            if (!splitDone) newPartitions.push(group);
        }
        partitions = newPartitions;
        history.push(partitions.map(p => new Set(p)));
    }

    return { partitions, history, splitHistory };
}

function buildMinimizedDFA(original, partitions) {
    const repOf = s => partitions.find(p => p.has(s));
    const repName = p => {
        const arr = [...p].sort();
        return arr.length === 1 ? arr[0] : '{' + arr.join(',') + '}';
    };

    const startPart = repOf(original.start);
    const finalParts = partitions.filter(p => [...p].some(s => original.finals.includes(s)));
    const states = partitions.map(p => repName(p));
    const start = repName(startPart);
    const finals = finalParts.map(p => repName(p));

    const trans = {};
    for (const p of partitions) {
        const from = repName(p);
        trans[from] = {};
        const rep = [...p][0];
        for (const sym of original.alpha) {
            const target = original.trans[rep]?.[sym];
            if (target) {
                const targetPart = repOf(target);
                trans[from][sym] = repName(targetPart);
            }
        }
    }

    return { states, alpha: original.alpha, start, finals, trans };
}

function buildDFA() {
    hideError();
    stopPlay();

    dfa = parseDFA();
    if (!dfa) return;

    const reachable = computeReachable(dfa);
    const reachableStates = dfa.states.filter(s => reachable.has(s));
    const unreachableStates = dfa.states.filter(s => !reachable.has(s));

    const filteredDFA = {
        states: reachableStates,
        alpha: dfa.alpha,
        start: dfa.start,
        finals: dfa.finals.filter(s => reachable.has(s)),
        trans: Object.fromEntries(reachableStates.map(s => [s, dfa.trans[s] || {}]))
    };

    const { partitions, history, splitHistory } = hopcroft(
        filteredDFA.states, filteredDFA.alpha, filteredDFA.finals, filteredDFA.trans
    );

    const minDFA = buildMinimizedDFA(filteredDFA, partitions);

    steps = buildSteps(dfa, reachable, unreachableStates, filteredDFA, history, splitHistory, partitions, minDFA);
    currentStep = -1;

    document.getElementById('btn-next').disabled = false;
    document.getElementById('btn-restart').disabled = false;
    document.getElementById('btn-playpause').disabled = false;
    document.getElementById('ba-panel').style.display = 'none';
    document.getElementById('table-panel').style.display = 'none';
    
    // Reset side-by-side Layout on build
    document.getElementById('graphs-wrapper').classList.remove('side-by-side');
    document.getElementById('min-graph-panel').style.display = 'none';

    updateStepIndicator();
    renderInitialDFA(dfa);
    setExplanation('DFA loaded. Press <strong>Next step</strong> or <strong>Play</strong> to begin minimization.');
    updateCounter();
}

function buildSteps(original, reachable, unreachable, filtered, history, splitHistory, finalPartitions, minDFA) {
    const steps = [];

    steps.push({
        type: 'start',
        title: 'Original DFA',
        explanation: `We start with a DFA of <strong>${original.states.length} states</strong> over alphabet {${original.alpha.join(', ')}}. Our goal is to find the smallest equivalent DFA. Click next to begin.`,
        dfa: original,
        highlight: null,
        unreachable: []
    });

    steps.push({
        type: 'reachable',
        title: 'Remove unreachable states',
        explanation: unreachable.length === 0
            ? `All states are reachable from start state <strong>${original.start}</strong>. No states to remove.`
            : `Starting from <strong>${original.start}</strong>, we can reach: ${[...reachable].map(s=>`<strong>${s}</strong>`).join(', ')}. States <strong>${unreachable.join(', ')}</strong> are unreachable and can be removed.`,
        dfa: original,
        highlight: [...reachable],
        unreachable: unreachable
    });

    steps.push({
        type: 'initial_partition',
        title: 'Initial partitioning',
        explanation: `Divide all reachable states into two groups: <strong>final states</strong> F = {${filtered.finals.join(', ')}} and <strong>non-final states</strong> NF = {${filtered.states.filter(s=>!filtered.finals.includes(s)).join(', ')}}. States in different groups cannot be equivalent.`,
        dfa: filtered,
        partitions: [new Set(filtered.finals), new Set(filtered.states.filter(s=>!filtered.finals.includes(s)))],
        highlight: null
    });

    for (let i = 1; i < history.length; i++) {
        const split = splitHistory[i-1];

        steps.push({
            type: 'refine',
            title: `Refinement — iteration ${i}`,
            explanation: split
                ? `Group {${[...split.group].join(', ')}} on symbol <strong>"${split.symbol}"</strong> transitions to different partitions, so we split it into: ${split.splits.map(g=>`{${g.join(', ')}}`).join(' and ')}.`
                : `No more splits possible. Partition is stable.`,
            dfa: filtered,
            partitions: history[i],
            splitGroup: split ? split.group : null,
            splitSymbol: split ? split.symbol : null,
            highlight: split ? split.splits : null
        });
    }

    if (history.length === 1) {
        steps.push({
            type: 'refine',
            title: 'Refinement — iteration 1',
            explanation: `The initial partition is already stable — no further splits needed.`,
            dfa: filtered,
            partitions: history[0],
            splitGroup: null,
            splitSymbol: null,
            highlight: null
        });
    }

    steps.push({
        type: 'merge',
        title: 'Merge equivalent states',
        explanation: `Final partitions: ${finalPartitions.map(p=>`{${[...p].join(', ')}}`).join(', ')}. States in the same partition are equivalent and can be merged into one representative state.`,
        dfa: filtered,
        partitions: finalPartitions,
        merging: true
    });

    steps.push({
        type: 'result',
        title: 'Minimized DFA',
        explanation: `Minimization complete. The DFA was reduced from <strong>${original.states.length} states</strong> to <strong>${minDFA.states.length} states</strong>${original.states.length === minDFA.states.length ? ' — it was already minimal!' : '.'}`,
        dfa: filtered,
        minDFA: minDFA,
        partitions: finalPartitions
    });

    return steps;
}

function restart() {
    stopPlay();
    currentStep = -1;
    document.getElementById('ba-panel').style.display = 'none';
    document.getElementById('table-panel').style.display = 'none';
    
    // Reset side-by-side
    document.getElementById('graphs-wrapper').classList.remove('side-by-side');
    document.getElementById('min-graph-panel').style.display = 'none';
    
    document.getElementById('btn-prev').disabled = true;
    document.getElementById('btn-next').disabled = false;
    renderInitialDFA(dfa);
    setExplanation('Restarted. Press <strong>Next step</strong> to begin again.');
    updateStepIndicator();
    updateCounter();
}

function prevStep() {
    stopPlay();
    if (currentStep > 0) {
        currentStep--;
        renderStep(currentStep);
    }
}

function nextStep() {
    if (currentStep < steps.length - 1) {
        currentStep++;
        renderStep(currentStep);
    }
    if (currentStep === steps.length - 1) stopPlay();
}

function togglePlay() {
    if (playing) stopPlay();
    else startPlay();
}

function startPlay() {
    playing = true;
    document.getElementById('btn-playpause').textContent = '⏸';
    scheduleNext();
}

function stopPlay() {
    playing = false;
    clearTimeout(playTimer);
    document.getElementById('btn-playpause').textContent = '▶';
}

function scheduleNext() {
    if (!playing) return;
    const speed = parseInt(document.getElementById('speed-slider').value);
    const delay = [1800, 1400, 1000, 700, 400][speed - 1];
    playTimer = setTimeout(() => {
        if (currentStep < steps.length - 1) {
            nextStep();
            if (currentStep < steps.length - 1) scheduleNext();
            else stopPlay();
        } else stopPlay();
    }, delay);
}

function renderStep(idx) {
    const step = steps[idx];

    document.getElementById('btn-prev').disabled = idx === 0;
    document.getElementById('btn-next').disabled = idx === steps.length - 1;

    setExplanation(step.explanation);
    updateStepIndicator(idx);
    updateCounter();

    // Default: Ensure side-by-side is OFF unless it's the result step
    if (step.type !== 'result') {
        document.getElementById('graphs-wrapper').classList.remove('side-by-side');
        document.getElementById('min-graph-panel').style.display = 'none';
    }

    if (step.type === 'start') {
        renderDFAGraph('dfa-svg', step.dfa, { mode: 'normal' });
        document.getElementById('table-panel').style.display = 'none';
        document.getElementById('ba-panel').style.display = 'none';
    } else if (step.type === 'reachable') {
        renderDFAGraph('dfa-svg', step.dfa, { mode: 'reachable', highlight: step.highlight, unreachable: step.unreachable });
        document.getElementById('table-panel').style.display = 'none';
        document.getElementById('ba-panel').style.display = 'none';
    } else if (step.type === 'initial_partition') {
        renderDFAGraph('dfa-svg', step.dfa, { mode: 'partition', partitions: step.partitions });
        renderPartitionTable(step.partitions, step.dfa, null, null);
        document.getElementById('table-panel').style.display = 'block';
        document.getElementById('table-title').textContent = 'Initial partition';
        document.getElementById('ba-panel').style.display = 'none';
    } else if (step.type === 'refine') {
        renderDFAGraph('dfa-svg', step.dfa, { mode: 'partition', partitions: step.partitions, splitGroup: step.splitGroup });
        renderPartitionTable(step.partitions, step.dfa, step.splitGroup, step.splitSymbol);
        document.getElementById('table-panel').style.display = 'block';
        document.getElementById('table-title').textContent = step.title;
        document.getElementById('ba-panel').style.display = 'none';
    } else if (step.type === 'merge') {
        renderDFAGraph('dfa-svg', step.dfa, { mode: 'merge', partitions: step.partitions });
        renderPartitionTable(step.partitions, step.dfa, null, null);
        document.getElementById('table-panel').style.display = 'block';
        document.getElementById('table-title').textContent = 'Final partitions — merging';
        document.getElementById('ba-panel').style.display = 'none';
    } else if (step.type === 'result') {
        // TRIGGER SIDE-BY-SIDE LAYOUT
        document.getElementById('graphs-wrapper').classList.add('side-by-side');
        document.getElementById('min-graph-panel').style.display = 'block';

        renderDFAGraph('dfa-svg', step.dfa, { mode: 'merge', partitions: step.partitions });
        renderMinimizedDFA(step.minDFA, step.dfa);
        document.getElementById('table-panel').style.display = 'none';
        document.getElementById('ba-panel').style.display = 'block';
        renderBeforeAfter(dfa, step.minDFA);
    }
}

function setExplanation(html) {
    const el = document.getElementById('explanation');
    el.style.opacity = '0';
    el.style.transform = 'translateY(5px)';
    setTimeout(() => {
        el.innerHTML = html;
        el.style.opacity = '1';
        el.style.transform = 'translateY(0)';
    }, 150); 
}

function updateCounter() {
    const total = steps.length;
    const cur = currentStep < 0 ? 0 : currentStep + 1;
    document.getElementById('step-counter').textContent = `${cur} / ${total}`;
    document.getElementById('progress-fill').style.width = total ? (cur / total * 100) + '%' : '0%';
}

function updateStepIndicator(active) {
    const stepNames = ['Start', 'Reachable', 'Partition', 'Refine', 'Merge', 'Result'];
    const stepTypes = ['start', 'reachable', 'initial_partition', 'refine', 'merge', 'result'];
    const container = document.getElementById('step-indicator');
    container.innerHTML = '';

    const seen = new Set();
    const stepDots = [];
    for (const t of stepTypes) {
        if (!seen.has(t)) {
            seen.add(t);
            const idx = steps.findIndex(s => s.type === t);
            stepDots.push({ type: t, label: stepNames[stepTypes.indexOf(t)], idx });
        }
    }

    stepDots.forEach((dot, i) => {
        const div = document.createElement('div');
        div.className = 'step-dot';
        const isDone = active !== undefined && dot.idx !== -1 && dot.idx < active;
        const isActive = active !== undefined && steps[active]?.type === dot.type;
        if (isDone) div.classList.add('done');
        if (isActive) div.classList.add('active');

        div.innerHTML = `<span class="dot"></span>${dot.label}`;
        container.appendChild(div);

        if (i < stepDots.length - 1) {
            const sep = document.createElement('span');
            sep.className = 'step-sep';
            sep.textContent = '—';
            container.appendChild(sep);
        }
    });
}

function layoutStates(states, width, height) {
    const n = states.length;
    const cx = width / 2, cy = height / 2;
    const r = Math.min(width, height) * 0.35;
    const positions = {};

    if (n === 1) {
        positions[states[0]] = { x: cx, y: cy };
    } else if (n === 2) {
        positions[states[0]] = { x: cx - r * 0.6, y: cy };
        positions[states[1]] = { x: cx + r * 0.6, y: cy };
    } else {
        states.forEach((s, i) => {
            const angle = (2 * Math.PI * i / n) - Math.PI / 2;
            positions[s] = { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
        });
    }
    return positions;
}

function partitionColor(partIdx) {
    // Bold Colors for Neo-Brutalism
    const colors = [
        { fill: '#E0B0FF', stroke: '#111111', text: '#111111' }, // Purple
        { fill: '#1DE9B6', stroke: '#111111', text: '#111111' }, // Teal
        { fill: '#FFD740', stroke: '#111111', text: '#111111' }, // Yellow
        { fill: '#FF5252', stroke: '#111111', text: '#111111' }, // Red
        { fill: '#448AFF', stroke: '#111111', text: '#111111' }, // Blue
        { fill: '#FFAB40', stroke: '#111111', text: '#111111' }, // Orange
    ];
    return colors[partIdx % colors.length];
}

function renderDFAGraph(svgId, dfaObj, opts = {}) {
    const svg = document.getElementById(svgId);
    const W = svg.parentElement.offsetWidth || 600;
    const H = parseInt(svg.getAttribute('height')) || 340;
    svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
    svg.innerHTML = '';

    const { mode = 'normal', highlight, unreachable = [], partitions, splitGroup, merging } = opts;

    const states = dfaObj.states;
    const pos = layoutStates(states, W, H);
    const R = 24;

    // THICK ARROW HEADS
    const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
    defs.innerHTML = `<marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M1 1L9 5L1 9" fill="none" stroke="#111111" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></marker>
    <marker id="arr-sel" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M1 1L9 5L1 9" fill="none" stroke="#FF5252" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></marker>`;
    svg.appendChild(defs);

    const getPartIdx = s => {
        if (!partitions) return -1;
        return partitions.findIndex(p => p.has(s));
    };

    const groupEdges = {};
    for (const from of states) {
        for (const sym of dfaObj.alpha) {
            const to = dfaObj.trans[from]?.[sym];
            if (!to) continue;
            const key = `${from}__${to}`;
            if (!groupEdges[key]) groupEdges[key] = { from, to, syms: [] };
            groupEdges[key].syms.push(sym);
        }
    }

    const edgeLayer = document.createElementNS('http://www.w3.org/2000/svg', 'g');
    svg.appendChild(edgeLayer);
    const nodeLayer = document.createElementNS('http://www.w3.org/2000/svg', 'g');
    svg.appendChild(nodeLayer);

    for (const key of Object.keys(groupEdges)) {
        const { from, to, syms } = groupEdges[key];
        const fp = pos[from], tp = pos[to];
        const label = syms.join(',');
        let isHighlighted = false;

        if (mode === 'refine' && splitGroup) {
            isHighlighted = splitGroup.has(from) || splitGroup.has(to);
        }

        if (from === to) {
            const lx = fp.x, ly = fp.y - R - 20;
            const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
            path.setAttribute('d', `M ${fp.x - 10} ${fp.y - R} C ${fp.x - 30} ${fp.y - R - 40} ${fp.x + 30} ${fp.y - R - 40} ${fp.x + 10} ${fp.y - R}`);
            path.setAttribute('fill', 'none');
            path.setAttribute('stroke', isHighlighted ? '#FF5252' : '#111111');
            path.setAttribute('stroke-width', '2.5'); // THICKER LINES
            path.setAttribute('marker-end', isHighlighted ? 'url(#arr-sel)' : 'url(#arr)');
            edgeLayer.appendChild(path);

            const t = document.createElementNS('http://www.w3.org/2000/svg', 'text');
            t.setAttribute('x', lx);
            t.setAttribute('y', fp.y - R - 44);
            t.setAttribute('text-anchor', 'middle');
            t.setAttribute('font-size', '13');
            t.setAttribute('font-family', "'JetBrains Mono', monospace");
            t.setAttribute('font-weight', '700');
            t.setAttribute('fill', isHighlighted ? '#FF5252' : '#111111');
            t.textContent = label;
            edgeLayer.appendChild(t);
        } else {
            const dx = tp.x - fp.x, dy = tp.y - fp.y;
            const dist = Math.sqrt(dx * dx + dy * dy);
            const nx = dx / dist, ny = dy / dist;
            const startX = fp.x + nx * R, startY = fp.y + ny * R;
            const endX = tp.x - nx * R, endY = tp.y - ny * R;

            const hasReverse = groupEdges[`${to}__${from}`];
            let d;
            if (hasReverse) {
                const ox = -ny * 18, oy = nx * 18;
                d = `M ${startX + ox} ${startY + oy} Q ${(startX + endX) / 2 + ox} ${(startY + endY) / 2 + oy} ${endX + ox} ${endY + oy}`;
            } else {
                d = `M ${startX} ${startY} L ${endX} ${endY}`;
            }

            const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
            path.setAttribute('d', d);
            path.setAttribute('fill', 'none');
            path.setAttribute('stroke', isHighlighted ? '#FF5252' : '#111111');
            path.setAttribute('stroke-width', '2.5'); // THICKER LINES
            path.setAttribute('marker-end', isHighlighted ? 'url(#arr-sel)' : 'url(#arr)');
            edgeLayer.appendChild(path);

            const mx = (fp.x + tp.x) / 2 + (hasReverse ? -ny * 24 : 0);
            const my = (fp.y + tp.y) / 2 + (hasReverse ? nx * 24 : -6);
            const lt = document.createElementNS('http://www.w3.org/2000/svg', 'text');
            lt.setAttribute('x', mx);
            lt.setAttribute('y', my);
            lt.setAttribute('text-anchor', 'middle');
            lt.setAttribute('font-size', '13');
            lt.setAttribute('font-family', "'JetBrains Mono', monospace");
            lt.setAttribute('font-weight', '700');
            lt.setAttribute('fill', isHighlighted ? '#FF5252' : '#111111');
            lt.textContent = label;
            
            // Add a white background to text so lines don't cross it
            const bbox = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
            // We append text first to get bbox in a real app, but here we just append text
            edgeLayer.appendChild(lt);
        }
    }

    const startArrow = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    const sp = pos[dfaObj.start];
    startArrow.setAttribute('x1', sp.x - R - 24);
    startArrow.setAttribute('y1', sp.y);
    startArrow.setAttribute('x2', sp.x - R - 2);
    startArrow.setAttribute('y2', sp.y);
    startArrow.setAttribute('stroke', '#111111');
    startArrow.setAttribute('stroke-width', '2.5');
    startArrow.setAttribute('marker-end', 'url(#arr)');
    edgeLayer.appendChild(startArrow);

    for (const s of states) {
        const { x, y } = pos[s];
        const partIdx = getPartIdx(s);
        const col = partIdx >= 0 ? partitionColor(partIdx) : null;
        const isFinal = dfaObj.finals.includes(s);
        const isUnreachable = unreachable.includes(s);
        const isHighlighted = highlight ? highlight.includes(s) : null;
        const inSplitGroup = splitGroup ? splitGroup.has(s) : false;

        const g = document.createElementNS('http://www.w3.org/2000/svg', 'g');
        g.setAttribute('class', 'state-node');

        let fillColor = '#ffffff';
        let strokeColor = '#111111';
        let strokeWidth = '3'; // THICKER CIRCLE BORDER
        let textColor = '#111111';

        if (mode === 'partition' || mode === 'merge') {
            if (col) {
                fillColor = col.fill;
                strokeColor = col.stroke;
                textColor = col.text;
            }
            if (inSplitGroup) {
                strokeColor = '#FF5252';
                strokeWidth = '4';
            }
        } else if (mode === 'reachable') {
            if (isHighlighted === true) {
                fillColor = '#1DE9B6';
                strokeColor = '#111111';
                textColor = '#111111';
            } else if (isUnreachable) {
                fillColor = '#F4F0EA';
                strokeColor = '#cccccc';
                textColor = '#cccccc';
                g.style.opacity = '0.5';
            }
        }

        const circle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
        circle.setAttribute('cx', x);
        circle.setAttribute('cy', y);
        circle.setAttribute('r', R);
        circle.setAttribute('fill', fillColor);
        circle.setAttribute('stroke', strokeColor);
        circle.setAttribute('stroke-width', strokeWidth);
        g.appendChild(circle);

        if (isFinal) {
            const inner = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
            inner.setAttribute('cx', x);
            inner.setAttribute('cy', y);
            inner.setAttribute('r', R - 6);
            inner.setAttribute('fill', 'none');
            inner.setAttribute('stroke', strokeColor);
            inner.setAttribute('stroke-width', '2');
            g.appendChild(inner);
        }

        const label = document.createElementNS('http://www.w3.org/2000/svg', 'text');
        label.setAttribute('x', x);
        label.setAttribute('y', y);
        label.setAttribute('text-anchor', 'middle');
        label.setAttribute('dominant-baseline', 'central');
        label.setAttribute('font-size', '14');
        label.setAttribute('font-family', "'JetBrains Mono', monospace");
        label.setAttribute('font-weight', '700');
        label.setAttribute('fill', textColor);
        label.textContent = s;
        g.appendChild(label);

        if (mode === 'merge' && merging !== false) {
            const partLabel = document.createElementNS('http://www.w3.org/2000/svg', 'text');
            partLabel.setAttribute('x', x);
            partLabel.setAttribute('y', y + R + 18);
            partLabel.setAttribute('text-anchor', 'middle');
            partLabel.setAttribute('font-size', '12');
            partLabel.setAttribute('font-weight', '700');
            partLabel.setAttribute('font-family', "'JetBrains Mono', monospace");
            partLabel.setAttribute('fill', '#111111');
            partLabel.textContent = `G${partIdx + 1}`;
            g.appendChild(partLabel);
        }

        nodeLayer.appendChild(g);
    }
}

function renderPartitionTable(partitions, dfaObj, splitGroup, splitSymbol) {
    const container = document.getElementById('table-content');
    const rows = [];

    partitions.forEach((p, i) => {
        const col = partitionColor(i);
        const members = [...p].sort();

        const transInfo = [];
        for (const sym of dfaObj.alpha) {
            const targetParts = members.map(s => {
                const t = dfaObj.trans[s]?.[sym];
                if (!t) return '—';
                const pi = partitions.findIndex(pp => pp.has(t));
                return pi >= 0 ? `G${pi + 1}` : '—';
            });
            const allSame = targetParts.every(tp => tp === targetParts[0]);
            transInfo.push({ sym, targetParts, split: !allSame && splitGroup && [...p].every(s => splitGroup.has(s)) && sym === splitSymbol });
        }

        const isSplit = splitGroup && members.every(s => splitGroup.has(s));

        rows.push({ idx: i, col, members, transInfo, isSplit });
    });

    let html = `<table class="partition-table"><thead><tr><th>Group</th><th>States</th>`;
    for (const sym of dfaObj.alpha) html += `<th>on "${sym}"</th>`;
    html += `</tr></thead><tbody>`;

    for (const row of rows) {
        const rowClass = row.isSplit ? 'split' : '';
        html += `<tr class="${rowClass}">`;
        html += `<td><span class="group-pill" style="background:${row.col.fill};color:${row.col.text}">G${row.idx + 1}</span></td>`;
        html += `<td>${row.members.map(s => `<span class="group-pill" style="background:${row.col.fill};color:${row.col.text}">${s}</span>`).join('')}</td>`;

        for (const t of row.transInfo) {
            const displayParts = row.members.map((s, si) => `${s}→${t.targetParts[si]}`).join(', ');
            html += `<td>${displayParts}${t.split ? ' ⚡' : ''}</td>`;
        }
        html += '</tr>';
    }

    html += '</tbody></table>';
    container.innerHTML = html;
}

function renderBeforeAfter(original, minDFA) {
    const bEl = document.getElementById('ba-before');
    const aEl = document.getElementById('ba-after');

    const origTrans = Object.values(original.trans).reduce((acc, t) => acc + Object.keys(t).length, 0);
    const minTrans = Object.values(minDFA.trans).reduce((acc, t) => acc + Object.keys(t).length, 0);
    const reduced = original.states.length > minDFA.states.length;

    bEl.innerHTML = `
        <div class="stat"><span>States</span><span class="val">${original.states.length}</span></div>
        <div class="stat"><span>Final states</span><span class="val">${original.finals.length}</span></div>
        <div class="stat"><span>Transitions</span><span class="val">${origTrans}</span></div>
        <div class="stat"><span>Alphabet size</span><span class="val">${original.alpha.length}</span></div>
    `;

    aEl.innerHTML = `
        <div class="stat"><span>States</span><span class="val highlight">${minDFA.states.length}</span></div>
        <div class="stat"><span>Final states</span><span class="val highlight">${minDFA.finals.length}</span></div>
        <div class="stat"><span>Transitions</span><span class="val highlight">${minTrans}</span></div>
        <div class="stat"><span>Alphabet size</span><span class="val">${minDFA.alpha.length}</span></div>
    `;

    if (reduced) {
        aEl.innerHTML += `<div style="margin-top:10px;font-size:12px; font-weight:700; color:var(--teal);">↓ ${original.states.length - minDFA.states.length} states removed</div>`;
    } else {
        aEl.innerHTML += `<div style="margin-top:10px;font-size:12px; font-weight:700; color:var(--ink3);">Already minimal</div>`;
    }
}

function renderMinimizedDFA(minDFA) {
    renderDFAGraph('min-svg', minDFA, { mode: 'normal' });
}

function renderInitialDFA(dfaObj) {
    renderDFAGraph('dfa-svg', dfaObj, { mode: 'normal' });
    document.getElementById('table-panel').style.display = 'none';
    document.getElementById('ba-panel').style.display = 'none';
}

window.addEventListener('load', () => {
    loadSample('simple');
    updateStepIndicator();
});