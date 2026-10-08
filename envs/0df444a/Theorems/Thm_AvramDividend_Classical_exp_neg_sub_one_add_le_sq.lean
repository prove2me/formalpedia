-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_neg_sub_one_add_le_sq
-- name    : AvramDividend.Classical.exp_neg_sub_one_add_le_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:17:20.785518+00:00
-- url     : https://prove2.me/theorems/0f3b6e17-f2be-4e63-8c1b-7663beea4f53
-- title:
--   Global quadratic upper bound for the negative exponential remainder
-- statement:
--   For every nonnegative real u, exp(-u)-1+u is at most u squared.
-- source:
--   Pinned Mathlib quadratic exponential remainder bound on the unit interval, combined with the elementary large-u bound.

import Mathlib

namespace AvramDividend.Classical

theorem exp_neg_sub_one_add_le_sq (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) - 1 + u ≤ u ^ 2 := by
  sorry

end AvramDividend.Classical
