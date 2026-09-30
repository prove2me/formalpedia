-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_sum_minTime_le_n_makespan
-- name    : AlgMechDesign.MinWork.sum_minTime_le_n_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:22:07.521991+00:00
-- url     : https://prove2.me/theorems/886177f4-6e9c-4797-b3bd-c27318fc8158
-- title:
--   Proof of Claim 4.3 — every allocation has make-span at least $\frac1n\sum_j \min_i t^i_j$
-- statement:
--   Let $n \ge 1$ and let $t$ be a positive type vector. For every allocation $y$ of the $k$ tasks (in particular an optimal allocation $\mathrm{opt}(t)$),
--   $$
--   g(y, t) \ge \frac{1}{n} \sum_{j=1}^k \min_i t^i_j .
--   $$
--   This is the lower half of the proof of Claim 4.3.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, proof of Claim 4.3, second inequality

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

/-- Proof of Claim 4.3, second bound: every allocation `y` (in particular an optimal one) has
make-span at least `(1/n) ∑_j minᵢ tⁱ_j`. -/
theorem sum_minTime_le_n_makespan {n k : ℕ} [NeZero n]
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin n) :
    1 / (n : ℝ) * ∑ j, minTime t j ≤ makespan t y := by sorry

end AlgMechDesign.MinWork
