-- Prove2me | Theorems.Thm_EulerianLE_lemma_29
-- name    : EulerianLE.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:03.873194+00:00
-- url     : https://prove2.me/theorems/12013877-87e5-41f0-a32f-71d1eb567ca4
-- title:
--   Lemma 29 — a round without a local leader outputs a valid configuration for the next round
-- statement:
--   Consider an execution of round $L_r$ ($r\ge1$) from a valid round-$r$ configuration in which no node is a local leader (the Check node has a port whose successor node is Counting, or there is no Check node). Then every node completes $L_r$, and the output configuration is a valid round-$(r+1)$ configuration.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: the standing assumptions of §C.2: r ≥ 1, a valid round-r configuration I, an arbitrary standalone execution of L_r on I → hypotheses `1 ≤ r`, `ValidConfig G ids r x`, a fair run `ρ` of `roundAlg G ids r` on `x`, an Eulerian network and injective identifiers; reason: these are the section's standing assumptions (p.36), stated as binders
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.4, p.41 (PDF p.43), Lemma 29

import Mathlib
import Definitions.Def_EulerianLE_relayTrail

namespace EulerianLE

/-- **Lemma 29** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.4, p.41, PDF p.43). If round `r` has no local
leader, then every node completes `L_r` and the output is a valid round-`(r + 1)` configuration.

**Formalization Note.** As in §C.2 (p.36), `r ≥ 1`, `x` is a valid round-`r` configuration on the
Eulerian network `G` with distinct identifiers, and `ρ` is an arbitrary standalone execution (fair run) of
`L_r` on `x`. Relay trails and successors refer to the input pairing `π⊤ = pairsOf G x`. "Round `r` has no local leader" (p.41: the
Check node has a port whose successor node is Counting, or there is no Check node) is: no node is a
local leader (`IsLocalLeader` includes being the Check node). The conclusion is that every node
completes, with the output tuple `y`, and `y` is valid for round `r + 1`. -/
theorem lemma_29 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ) (hid : Function.Injective ids)
    (r : ℕ) (hr : 1 ≤ r) (x : ∀ u, CIO G u) (hx : ValidConfig G ids r x)
    (ρ : Run ((roundAlg G ids r).progs x) (stdTag _)) (hρ : IsFair ρ)
    (hnl : ¬ ∃ u, IsLocalLeader ids r (pairsOf G x) u) :
    ∃ y, ρ.Outputs y ∧ ValidConfig G ids (r + 1) y := by sorry

end EulerianLE
