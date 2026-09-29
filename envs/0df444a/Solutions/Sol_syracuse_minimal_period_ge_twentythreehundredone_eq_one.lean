-- Prove2me | solution 1 for syracuse_minimal_period_ge_twentythreehundredone_eq_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:01:29.472067+00:00
-- url     : https://prove2.me/submissions/be0fdbbd-98cd-4170-bef0-2e47cc06acda
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_period_le_twentyninesixtyfive_eq_one
import Theorems.Thm_syracuse_minimal_period_ge_twentyninesixtysix_eq_one

/-- Least period at least 2301 splits at 2966: periods 2301..2965 are excluded outright by the
margin criterion at threshold 860564, and periods ≥ 2966 are the remaining frontier. -/
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 2301 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by
  rcases Nat.lt_or_ge p 2966 with h | h
  · exact syracuse_period_le_twentyninesixtyfive_eq_one m p hm (by omega) (by omega) hcyc
  · exact syracuse_minimal_period_ge_twentyninesixtysix_eq_one m p hm h hcyc hmin
