-- Prove2me | solution 1 for syracuse_minimal_period_ge_threehundredsix_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T07:07:06.695528+00:00
-- url     : https://prove2.me/submissions/fa1bfd08-493c-4bd8-8818-35f9d47757aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_ninehundredseventy_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_ninehundredseventyone_eq_one

/-- Least period at least 306 splits at 971: periods 306..970 are excluded outright by the margin
criterion at threshold 99781, and periods ≥ 971 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 306 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 971 with h | h
  · exact syracuse_period_le_ninehundredseventy_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_ninehundredseventyone_eq_one m p hm h hcyc hmin
