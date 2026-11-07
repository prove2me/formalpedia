-- Prove2me | Theorems.Thm_EulerianLE_lemma_25
-- name    : EulerianLE.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:42.258834+00:00
-- url     : https://prove2.me/theorems/97e0c35b-78eb-4f70-adb9-4a7f1860e412
-- title:
--   Lemma 25 — the probing loop of the Check node ends and classifies ports by their successors
-- statement:
--   Consider an execution of round $L_r$ from a valid round-$r$ configuration, and its Check node $u$ ($\mathrm{ID}_u=r-1$). The probing loop (Lines 3–11 of Program 4) of $u$ eventually ends, and when it has ended:
--
--   1. a port of $u$ is classified counting if and only if its successor node is Counting, and such a port was classified in the iteration that probed it;
--   2. every other port $i$ of $u$ has a port $j$ of $u$ as its successor, and the loop has probed exactly one of $i$ and $j$;
--   3. $W$ contains the arc $(i,j)$ exactly when $j$ is the successor of $i$, $i$ was probed and $j$ was not, and contains no arc twice.
--
--   The lemma is what the Check node learns from probing: whether every incident circuit has it as its only non-relay node (it is a local leader), and the probe directions that orient those circuits.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: the standing assumptions of §C.2: r ≥ 1, a valid round-r configuration I, an arbitrary standalone execution of L_r on I → hypotheses `1 ≤ r`, `ValidConfig G ids r x`, a fair run `ρ` of `roundAlg G ids r` on `x`, an Eulerian network and injective identifiers; reason: these are the section's standing assumptions (p.36), stated as binders
--   - encoding: "the loop eventually ends"; "probes"; "in the iteration that probes the port" → the instrumentation variables `probeDone` and `probed` (which no program reads) mark the end of the loop and the probed ports; a counting port has been probed; reason: only the probed port of an iteration can be classified counting in it, so a counting port classified in its own probing iteration is exactly a probed counting port
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.3, p.39 (PDF p.41), Lemma 25

import Mathlib
import Definitions.Def_EulerianLE_relayTrail

namespace EulerianLE

/-- **Lemma 25** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.3, p.39, PDF p.41). The probing loop (Lines
3–11 of Program 4) of `u` eventually ends. It classifies a port of `u` as counting if and only if the
successor node of the port is Counting, and it does so in the iteration that probes the port. Every
other port `i` has a port `j` of `u` as its successor; the loop probes exactly one of `i` and `j`. For any
two ports of `u` that are each other's successors, `W` contains one arc, from the probed one to the
unprobed one, and `W` contains no other arc.

**Formalization Note.** As in §C.2 (p.36), `r ≥ 1`, `x` is a valid round-`r` configuration on the
Eulerian network `G` with distinct identifiers, and `ρ` is an arbitrary standalone execution (fair run) of
`L_r` on `x`. Relay trails and successors refer to the input pairing `π⊤ = pairsOf G x`. `u` is the Check node of the round
(`ID_u = r − 1`). The variables `probeDone` (set right after the loop) and `probed` (set when an iteration
probes a port) record the end of the loop and the probed ports; the conclusion reads `u`'s classification
`pcls` and arcs `W` at a time after the loop has ended. "In the iteration that probes the port" is: a port
classified counting has been probed (only the probed port of an iteration can be classified counting
there). "One arc" is: `W` has no repeated entry. -/
theorem lemma_25 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ) (hid : Function.Injective ids)
    (r : ℕ) (hr : 1 ≤ r) (x : ∀ u, CIO G u) (hx : ValidConfig G ids r x)
    (ρ : Run ((roundAlg G ids r).progs x) (stdTag _)) (hρ : IsFair ρ)
    (u : G.V) (hu : ids u + 1 = r) :
    ∃ t st, roundStoreAt ρ u t = some st ∧ st.probeDone = true ∧
      (∀ i, st.pcls i = .counting ↔ SuccCounting ids r (pairsOf G x) ⟨u, i⟩) ∧
      (∀ i, st.pcls i = .counting → st.probed i = true) ∧
      (∀ i, ¬ SuccCounting ids r (pairsOf G x) ⟨u, i⟩ →
        ∃ j, succPort ids r (pairsOf G x) ⟨u, i⟩ = some ⟨u, j⟩ ∧ st.probed i ≠ st.probed j) ∧
      (∀ i j, (i, j) ∈ st.W ↔
        (succPort ids r (pairsOf G x) ⟨u, i⟩ = some ⟨u, j⟩ ∧ st.probed i = true ∧
          st.probed j = false)) ∧
      st.W.Nodup := by sorry

end EulerianLE
