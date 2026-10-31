-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strictPastClock_tendsto_left
-- name    : AvramDividend.Classical.avram_wave3_04_strictPastClock_tendsto_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T10:37:15.052023+00:00
-- url     : https://prove2.me/theorems/8ac0f261-7891-44a0-9c8e-46f7df1bbdc8
-- title:
--   Explicit countable strict-past clock tends to positive time from below
-- statement:
--   For every strictly positive nonnegative-real clock time t, the explicit countable approximating sequence t−t/(n+2) converges to t in the left neighbourhood filter. The terms lie strictly below t, and their remainders tend to zero. This is the exact time-indexing bridge for left limits of the genuinely controlled post-payment reserve, and imposes no artificial stochastic-integrator assumptions.
-- source:
--   Pinned Mathlib Analysis.SpecificLimits.Basic tendsto_const_div_atTop_nhds_zero_nat, tendsto_add_atTop_iff_nat and Filter.tendsto_nhdsWithin_iff. Successfully reached remote sentinel on job 48328512-41e8-423b-baed-23799edc438e, candidate SHA-256 86b3ec0094a05b99655299b3f8269e02766da152643715f89dbcbe7c8b53d814.

import Mathlib

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_strictPastClock_tendsto_left (t : ℝ≥0) (ht : 0 < t) :
    Filter.Tendsto (fun n : ℕ => t - t / ((n : ℝ≥0) + 2))
      Filter.atTop (nhdsWithin t (Set.Iio t)) := by sorry
