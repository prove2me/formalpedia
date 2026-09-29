-- Prove2me | solution 1 for syracuse_minimal_period_ge_eight_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:30:38.065235+00:00
-- url     : https://prove2.me/submissions/d834b99e-ad6a-4e86-8ea3-c6ab660524a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_sixteen_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_seventeen_eq_one

/-- Least period at least 8 splits at 17: periods 8..16 are excluded outright by the margin
criterion, and periods ≥ 17 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 8 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 17 with h17 | h17
  · exact syracuse_period_le_sixteen_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_seventeen_eq_one m p hm h17 hcyc hmin
