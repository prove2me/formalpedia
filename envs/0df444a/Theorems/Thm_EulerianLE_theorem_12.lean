-- Prove2me | Theorems.Thm_EulerianLE_theorem_12
-- name    : EulerianLE.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:03.761376+00:00
-- url     : https://prove2.me/theorems/0310bce6-7028-4c89-a1f4-07741318b609
-- title:
--   Theorem 12 — rounds compose and progress
-- statement:
--   Let $G$ be an Eulerian network with distinct identifiers and $1\le r\le\mathrm{ID}_{\max}+1$. Then round $L_r$ is composable on the class of all valid round-$r$ configurations. In every standalone execution from such a configuration:
--
--   1. every port makes exactly four pulse interactions (sends and consumptions);
--   2. if some node is Counting ($\mathrm{ID}_u\ge r$), every node completes and the output is a valid round-$(r+1)$ configuration;
--   3. otherwise every node completes and the output is a successful configuration.
--
--   This is the main technical theorem: each round is analysed on its own, and the rounds compose to Program 1.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: ports 1, …, deg(u) → ports `Fin deg` (0-based); the initial pairs (2h−1, 2h) become (2h, 2h+1); reason: a relabelling; lexicographic and smallest-port orders are unchanged
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.25 (PDF p.27), Theorem 12; proof App. C.6, p.46

import Mathlib
import Definitions.Def_EulerianLE_ValidConfig

namespace EulerianLE

/-- **Theorem 12** (Rounds compose and progress; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.25, PDF p.27;
proof App. C, p.46). Let `1 ≤ r ≤ IDmax + 1`. Then `L_r` is composable on valid round-`r` configurations.
On each of them, every port makes exactly four pulse interactions; if some node is Counting, the output
is a valid round-`(r + 1)` configuration, and otherwise it is a successful configuration.

**Formalization Note.** The network is Eulerian with distinct identifiers (§2, p.6). The class of
inputs is the set of **all** valid round-`r` configurations, not only those reachable by the algorithm.
"Every port makes exactly four pulse interactions": in every standalone execution (fair run), the
number of sends and consumptions at each port is eventually exactly `4`. The output claims include that
every node completes. -/
theorem theorem_12 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ)
    (hid : Function.Injective ids) (r : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ IDmax G ids + 1) :
    IsComposable (roundAlg G ids r) {x | ValidConfig G ids r x} ∧
    ∀ x, ValidConfig G ids r x → ∀ ρ : Run ((roundAlg G ids r).progs x) (stdTag _), IsFair ρ →
      (∀ p, ∃ t, ∀ t', t ≤ t' → (ρ.cfg t').sent p + (ρ.cfg t').consumed p = 4) ∧
      ((∃ u, r ≤ ids u) → ∃ y, ρ.Outputs y ∧ ValidConfig G ids (r + 1) y) ∧
      ((∀ u, ids u < r) → ∃ y ℓ, ρ.Outputs y ∧ SuccessfulWith G y ℓ) := by sorry

end EulerianLE
