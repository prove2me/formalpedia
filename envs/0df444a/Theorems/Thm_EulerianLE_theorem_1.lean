-- Prove2me | Theorems.Thm_EulerianLE_theorem_1
-- name    : EulerianLE.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:41.140034+00:00
-- url     : https://prove2.me/theorems/4410e811-d389-4088-bb49-7e9cc8f6b576
-- title:
--   Theorem 1 — Program 1 elects a unique leader on every Eulerian network with exactly $4|E|(\mathrm{ID}_{\max}+1)$ pulses, quiescently, the leader last
-- statement:
--   There is a deterministic uniform content-oblivious leader-election algorithm, Program 1, with the following property. Let $G=(V,E)$ be an Eulerian network with distinct identifiers $\mathrm{ID}:V\to\mathbb N$, and let every node $u$ run Program 1 with its identifier and degree. Then
--
--   1. a standalone execution exists;
--   2. in every standalone execution there is a node $\ell$ that completes with output Leader while every other node completes with output Non-Leader;
--   3. the execution terminates quiescently: every pulse sent to a node is consumed before that node completes;
--   4. the leader $\ell$ completes strictly after every other node;
--   5. the total number of pulses sent is exactly
--   $$4\,|E|\,(\mathrm{ID}_{\max}+1).$$
--
--   Quiescent termination, with the leader last, is what allows the leader election to be composed with the simulator of Censor-Hillel, Cohen, Gelles and Sela, giving content-oblivious computation on every Eulerian network without a preassigned leader.
--
--   Differences from the source:
--   - generalization: there is a deterministic uniform content-oblivious algorithm → the named algorithm Program 1 (`program1 (ids v) (G.deg v)`, a function of the node's identifier and degree only); reason: the source's existential follows with Program 1 as the witness, which the paper's proof uses; determinism, content-obliviousness and uniformity hold by construction
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: ports 1, …, deg(u) → ports `Fin deg` (0-based); the initial pairs (2h−1, 2h) become (2h, 2h+1); reason: a relabelling; lexicographic and smallest-port orders are unchanged
--   - reading: elects a unique leader, terminates, sends 4|E|(IDmax + 1) pulses (in every execution) → a fair run exists, and every fair run has these properties; reason: excludes a vacuous statement over an empty set of executions (paper.md decision 8)
--   - encoding: "quiescently terminates"; "the last node to terminate"; "sends N pulses" → `Run.Quiescent` (per node at its completion); strictly earlier completion steps; total sends eventually equal to N; reason: footnote 1, p.2: "every pulse is consumed before its destination node has terminated"; the count is an equality
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §1.1, pp.1–2 (PDF pp.3–4), Theorem 1; proof §5.2, p.26

import Mathlib
import Definitions.Def_EulerianLE_IsLeaderElectionFor

namespace EulerianLE

/-- **Theorem 1** (Main; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §1.1, pp.1–2, PDF pp.3–4). There is a
deterministic uniform content-oblivious leader-election algorithm that, on every Eulerian network
`G = (V, E)` with unique identifiers, elects a unique leader and sends `4|E|(IDmax + 1)` pulses, where
`IDmax` is the largest identifier in `G`. The algorithm quiescently terminates and the elected leader is
the last node to terminate.

**Formalization Note.** The algorithm is named: Program 1 (`program1`), which gives the printed
existential. It is deterministic (an automaton with a step function), content-oblivious (it sees only
queue-test outcomes), and uniform (`program1 id deg` depends only on the node's identifier and degree,
with no bound on `n`, `|E|` or the identifiers). Networks are port-numbered multigraphs (self-loops and
parallel edges allowed), which include every simple Eulerian graph with every port numbering;
identifiers are arbitrary distinct natural numbers (`0` included). Executions are fair runs of the
gated asynchronous model (`Run`, `IsFair`); `IsLeaderElectionFor` gives existence of an execution, a
unique leader in every execution, quiescence, and the leader strictly last; the pulse count is an
equality on every execution. -/
theorem theorem_1 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ)
    (hid : Function.Injective ids) :
    IsLeaderElectionFor G (fun v => program1 (ids v) (G.deg v)) ∧
    ∀ ρ : Run (fun v => program1 (ids v) (G.deg v)) (stdTag _), IsFair ρ →
      ρ.SendsExactly (4 * G.edgeCount * (IDmax G ids + 1)) := by sorry

end EulerianLE
