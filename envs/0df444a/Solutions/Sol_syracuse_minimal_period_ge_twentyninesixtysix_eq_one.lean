-- Prove2me | solution 1 for syracuse_minimal_period_ge_twentyninesixtysix_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:43:18.581202+00:00
-- url     : https://prove2.me/submissions/bbffa0a1-5668-4f0a-af62-38c0a9c7bbdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_thirtysixthirty_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_thirtysixthirtyone_eq_one

/-- Least period at least 2966 splits at 3631: periods 2966..3630 are excluded outright by the
margin criterion at threshold 1166400, and periods ≥ 3631 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 2966 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 3631 with h | h
  · exact syracuse_period_le_thirtysixthirty_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_thirtysixthirtyone_eq_one m p hm h hcyc hmin
