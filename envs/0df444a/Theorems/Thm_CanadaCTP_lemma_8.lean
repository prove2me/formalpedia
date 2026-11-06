-- Prove2me | Theorems.Thm_CanadaCTP_lemma_8
-- name    : CanadaCTP.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:34.816282+00:00
-- url     : https://prove2.me/theorems/44bbf244-84df-44b3-8e98-e81a461cc7fb
-- title:
--   Lemma 8 — PathExplorer solves PathOpt optimally in time $O(d^2)$
-- statement:
--   There is a constant $C$ such that for every path $X=(X_j)_{j\in[m]}$ and every budget $b\ge0$, PathExplorer on $(X,b)$ returns an optimal coin vector (as in Lemma 7) using at most
--   $$
--   C\,(1+d)^2,\qquad d=\sum_{j=1}^m|\operatorname{supp}X_j|,
--   $$
--   counted operations.
--
--   It bounds the per-phase planning cost of ParallelTraveller.
--
--   **Formalization Note** Time is the number of unit-cost operations counted by the published counter `CapacitatedAssort.General.Work` (arithmetic, comparisons, reads, writes, loop dispatches). $O(d^2)$ is written $C(1+d)^2$, which is equivalent for $d\ge1$ and not an impossible $0$ bound at $d=0$.
--
--   Differences from the source:
--   - encoding: time O(d²) → ∃ C, peOps X b ≤ C·(1 + d)², one C for all paths and budgets; reason: unit-cost operation count of the named program; equivalent for d ≥ 1 and avoids the impossible bound 0 at d = 0
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 8, p.14; proof pp.38–39

import Mathlib
import Definitions.Def_CanadaCTP_PathExplorer

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 8, p.14 (proof pp.38–39): PathExplorer solves PathOpt optimally in time
`O(d²)`, `d = Σ_j |supp(X_j)|`, with one constant for all paths and budgets.

**Formalization Note.** Time is the number of unit-cost operations counted by
`CapacitatedAssort.General.Work`; `O(d²)` is `≤ C·(1 + d)²` (equivalent for `d ≥ 1`, and not an
impossible `0` bound at `d = 0`). -/
theorem lemma_8 : ∃ C : ℝ, ∀ {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ), 0 ≤ b →
    (InCOIN X (peOut X b) ∧
      expCost (pathInst X) (coinPolicy X (peOut X b)) ≤ ENNReal.ofReal b ∧
      (arrProb (pathInst X) (coinPolicy X (peOut X b))).toReal = probX X b) ∧
    (peOps X b : ℝ) ≤ C * (1 + (dX X : ℝ)) ^ 2 := by sorry

end CanadaCTP
