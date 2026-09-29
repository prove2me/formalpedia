-- Prove2me | solution 1 for syracuse_minimal_period_ge_ninetyfour_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:12:09.478609+00:00
-- url     : https://prove2.me/submissions/76595820-7b2f-4c8b-9883-62e24ab85cba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_onehundredninetynine_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_twohundred_eq_one

/-- Least period at least 94 splits at 200: periods 94..199 are excluded outright by the margin
criterion at threshold 6725, and periods ≥ 200 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 94 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 200 with h | h
  · exact syracuse_period_le_onehundredninetynine_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_twohundred_eq_one m p hm h hcyc hmin
