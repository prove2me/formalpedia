-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_zero_extended_log_continuous_at_zero
-- name    : AvramDividend.Classical.avram_wave3_01_zero_extended_log_continuous_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:12:26.769987+00:00
-- url     : https://prove2.me/theorems/e665ceef-e21e-46a5-a462-49bc08ad07cb
-- title:
--   Zero-extended logarithm of an ENNReal factor tending to one is continuous
-- statement:
--   If an extended nonnegative real factor F(t) tends to one as positive real t decreases to zero, then the real logarithm of its finite real conversion, extended by zero on nonpositive t, is continuous at zero. This uses ENNReal.toReal continuity at one, ordinary log continuity at one, and the left/right neighbourhood criterion. It is the exact topological adapter between the original Lévy first-record factor and the positive semigroup exponential law.
-- source:
--   Mathlib.Topology.Order.LeftRight.continuousAt_iff_continuous_left'_right' and ENNReal.continuousAt_toReal; Avram genuine first-record small-height limit.

import Mathlib
open Filter Topology Set
open scoped Topology ENNReal NNReal

theorem AvramDividend.Classical.avram_wave3_01_zero_extended_log_continuous_at_zero
    (F : ℝ → ℝ≥0∞)
    (hone : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ≥0∞))) :
    ContinuousAt (fun h : ℝ =>
      if 0 < h then Real.log ((F h).toReal) else 0) 0 := by sorry
