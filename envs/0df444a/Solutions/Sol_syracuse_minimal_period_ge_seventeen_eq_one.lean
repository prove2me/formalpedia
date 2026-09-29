-- Prove2me | solution 1 for syracuse_minimal_period_ge_seventeen_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:48:19.847327+00:00
-- url     : https://prove2.me/submissions/84d9f72d-21be-4a1f-9cbf-013a282ceed7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_ninetythree_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_ninetyfour_eq_one

/-- Least period at least 17 splits at 94: periods 17..93 are excluded outright by the margin
criterion at threshold 1193, and periods ≥ 94 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 17 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 94 with h94 | h94
  · exact syracuse_period_le_ninetythree_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_ninetyfour_eq_one m p hm h94 hcyc hmin
