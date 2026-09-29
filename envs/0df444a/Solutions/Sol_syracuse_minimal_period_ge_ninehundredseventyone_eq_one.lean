-- Prove2me | solution 1 for syracuse_minimal_period_ge_ninehundredseventyone_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:30:52.273625+00:00
-- url     : https://prove2.me/submissions/79e54e6b-1200-4c6b-a414-230381e46416
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_sixteenthirtyfive_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_sixteenthirtysix_eq_one

/-- Least period at least 971 splits at 1636: periods 971..1635 are excluded outright by the
margin criterion at threshold 330750, and periods ≥ 1636 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 971 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 1636 with h | h
  · exact syracuse_period_le_sixteenthirtyfive_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_sixteenthirtysix_eq_one m p hm h hcyc hmin
