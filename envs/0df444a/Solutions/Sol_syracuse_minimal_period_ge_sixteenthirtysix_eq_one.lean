-- Prove2me | solution 1 for syracuse_minimal_period_ge_sixteenthirtysix_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:45:40.808338+00:00
-- url     : https://prove2.me/submissions/76b1c218-c823-4f57-b0b6-2c60c5b8e682
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_twentythreehundred_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_twentythreehundredone_eq_one

/-- Least period at least 1636 splits at 2301: periods 1636..2300 are excluded outright by the
margin criterion at threshold 583288, and periods ≥ 2301 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 1636 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 2301 with h | h
  · exact syracuse_period_le_twentythreehundred_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_twentythreehundredone_eq_one m p hm h hcyc hmin
