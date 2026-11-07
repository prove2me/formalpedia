-- Prove2me | Theorems.Thm_EulerianLE_corollary_15
-- name    : EulerianLE.corollary_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:21.731205+00:00
-- url     : https://prove2.me/theorems/8366f9b2-bd0f-4d7e-819d-d6b47060e71a
-- title:
--   Corollary 15 — Program 1 sends exactly $4|E|(\mathrm{ID}_{\max}+1)$ pulses
-- statement:
--   Let $G$ be an Eulerian network with distinct identifiers. In every standalone execution of Program 1 on $G$, the total number of pulses sent is exactly
--   $$4\,|E|\,(\mathrm{ID}_{\max}+1).$$
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: "sends exactly N pulses" → the total number of sends is eventually equal to N (and never changes afterwards); reason: sends are counted from the start; equality, not a bound
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.26 (PDF p.28), Corollary 15

import Mathlib
import Definitions.Def_EulerianLE_program1

namespace EulerianLE

/-- **Corollary 15** (Pulse complexity; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.26, PDF p.28). Program 1
sends exactly `4|E|(IDmax + 1)` pulses.

**Formalization Note.** On every Eulerian network with distinct identifiers (§2, p.6), in every
standalone execution (fair run), the total number of sends is eventually exactly `4|E|(IDmax + 1)`
(equality, not a bound). -/
theorem corollary_15 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ)
    (hid : Function.Injective ids) :
    ∀ ρ : Run (fun v => program1 (ids v) (G.deg v)) (stdTag _), IsFair ρ →
      ρ.SendsExactly (4 * G.edgeCount * (IDmax G ids + 1)) := by sorry

end EulerianLE
