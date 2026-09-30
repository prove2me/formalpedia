-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_makespan_le_sum_minTime
-- name    : AlgMechDesign.MinWork.makespan_le_sum_minTime
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:19:45.649169+00:00
-- url     : https://prove2.me/theorems/7f7388d9-e767-4b14-b1ef-d4e8989f41d2
-- title:
--   Proof of Claim 4.3 — MinWork's make-span is at most the sum of minimal times
-- statement:
--   Let $n \ge 1$, let $x(\cdot)$ be any MinWork allocation rule and $t$ a positive type vector. Then the make-span of the MinWork allocation is at most the total of the minimal times:
--   $$
--   g(x(t), t) \le \sum_{j=1}^k \min_i t^i_j .
--   $$
--   This is the upper half of the proof of Claim 4.3.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 177, proof of Claim 4.3, first inequality

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

/-- Proof of Claim 4.3, first bound: the make-span of the MinWork allocation is at most
`∑_j minᵢ tⁱ_j`. -/
theorem makespan_le_sum_minTime {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) :
    makespan t (alloc t) ≤ ∑ j, minTime t j := by sorry

end AlgMechDesign.MinWork
