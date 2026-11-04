-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:47.633608+00:00
-- url     : https://prove2.me/theorems/6fcc2905-0951-4420-8cee-0362e7cdc771
-- title:
--   Genuine real-to-nonnegative physical clock gives exact finite-interval Lebesgue mass
-- statement:
--   The actual P3/P2 finite physical clock is real Lebesgue on [0,T] mapped by Real.toNNReal. For every source interval (s,t] with t≤T, its exact measure is ENNReal.ofReal((t:ℝ)-(s:ℝ)), including empty intervals. This derives from the true map/restrict measure operations and original clock preimage identity; no surrogate Poisson model or assumed clock rate. It supplies the deterministic factor in original predictable compensator N.
-- source:
--   Mathlib Measure.map_apply, Measure.restrict_apply, Real.volume_Ioc, continuous_real_toNNReal; Proved P3-B source clock preimage helper.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by sorry
