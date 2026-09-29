-- Prove2me | solution 1 for syracuse_minimal_period_ge_twohundred_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:36:02.665278+00:00
-- url     : https://prove2.me/submissions/7d20d050-cccd-45ca-baa6-4a5410aed59a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_twohundredfiftytwo_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_twohundredfiftythree_eq_one

/-- Least period at least 200 splits at 253: periods 200..252 are excluded outright by the margin
criterion at threshold 12825, and periods ≥ 253 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 200 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 253 with h | h
  · exact syracuse_period_le_twohundredfiftytwo_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_twohundredfiftythree_eq_one m p hm h hcyc hmin
