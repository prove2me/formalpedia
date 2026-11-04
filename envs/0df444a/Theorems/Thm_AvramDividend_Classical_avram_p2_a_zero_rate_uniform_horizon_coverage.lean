-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_horizon_coverage
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_horizon_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:36:37.173646+00:00
-- url     : https://prove2.me/theorems/9a1f9b24-9408-4ab1-8c81-7713911557c2
-- title:
--   Exact total horizon covered by n+1 original equal-width cells
-- statement:
--   For every nonnegative horizon T and natural n, the product of n+1 and uniform source mesh T/(n+1) is exactly T in NNReal, including T=0. This elementary identity is required to specialise the established original small-time negative-tail probability mass bound under total-duration constraint and to identify the endpoint of the last source grid cell.

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_horizon_coverage
    (T : ℝ≥0) (n : ℕ) :
    (((n : ℝ≥0) + 1) * (T / ((n : ℝ≥0) + 1))) = T := by sorry
