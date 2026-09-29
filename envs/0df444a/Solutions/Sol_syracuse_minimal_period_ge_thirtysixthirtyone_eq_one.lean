-- Prove2me | solution 1 for syracuse_minimal_period_ge_thirtysixthirtyone_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T23:28:37.926113+00:00
-- url     : https://prove2.me/submissions/bf68ec12-6a6f-4af9-96f2-7bc245290a72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_fortytwoninetyfive_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_fortytwoninetysix_eq_one

/-- Least period at least 3631 splits at 4296: periods 3631..4295 are excluded outright by the
margin criterion at threshold 1505449, and periods ≥ 4296 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 3631 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 4296 with h | h
  · exact syracuse_period_le_fortytwoninetyfive_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_fortytwoninetysix_eq_one m p hm h hcyc hmin
