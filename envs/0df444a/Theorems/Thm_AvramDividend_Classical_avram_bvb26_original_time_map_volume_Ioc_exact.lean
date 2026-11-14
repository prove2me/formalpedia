-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_time_map_volume_Ioc_exact
-- name    : AvramDividend.Classical.avram_bvb26_original_time_map_volume_Ioc_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:01:06.81166+00:00
-- url     : https://prove2.me/theorems/18508f5d-a214-453d-915a-09de0a1ae82b
-- title:
--   Original finite physical-horizon mapped real Lebesgue clock gives exact NNReal Ioc measure
-- statement:
--   The actual physical time measure of the BV source is real Lebesgue volume restricted to the real finite interval from zero to T and pushed forward to nonnegative time through Real.toNNReal. On every nonnegative-time interval Ioc(s,t) within T, the mapped measure of that interval equals the original real Lebesgue measure of Ioc(s,t) after casting endpoints. This is the exact source clock transport needed for the stopped negative-mark compensator K. It uses the already Proved exact original physical time-map preimage theorem and preserves the source measure without introducing an alternative probability clock.
-- source:
--   Proved avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage 24a903f6; pinned Mathlib Measure.map_apply, Measure.restrict_apply, measurable_real_toNNReal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb26_original_time_map_volume_Ioc_exact
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (((volume : Measure ℝ).restrict (Icc (0 : ℝ) (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    (volume : Measure ℝ) (Ioc (s : ℝ) (t : ℝ)) := by sorry
