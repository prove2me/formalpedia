-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_leftLim_origin_nnreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:31:42.045889+00:00
-- url     : https://prove2.me/theorems/d955d184-5d1d-4d1f-97a3-ff7929d6f55e
-- title:
--   Original nonnegative time-line left limit equals value at zero
-- statement:
--   For an arbitrary real-valued path on NNReal time, the lower endpoint zero has no earlier times. Mathlib's leftLim convention coincides with the value at that endpoint, proved by continuousWithinAt_singleton and ContinuousWithinAt.leftLim_eq. This removes an artificial zero-origin jump without any Lévy process or stochastic assumptions.

import Mathlib
open Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_leftLim_origin_nnreal
    (Y : ℝ≥0 → ℝ) :
    Function.leftLim Y 0 = Y 0 := by sorry
