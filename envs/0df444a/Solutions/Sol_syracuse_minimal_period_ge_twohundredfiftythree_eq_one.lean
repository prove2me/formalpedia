-- Prove2me | solution 1 for syracuse_minimal_period_ge_twohundredfiftythree_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:56:49.336394+00:00
-- url     : https://prove2.me/submissions/afa543ee-039e-46a6-a432-b6caf471c161
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_threehundredfive_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_threehundredsix_eq_one

/-- Least period at least 253 splits at 306: periods 253..305 are excluded outright by the margin
criterion at threshold 27114, and periods ≥ 306 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 253 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 306 with h | h
  · exact syracuse_period_le_threehundredfive_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_threehundredsix_eq_one m p hm h hcyc hmin
