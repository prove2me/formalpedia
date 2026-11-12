-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_time_map_integral
-- name    : AvramDividend.Classical.avram_bvb_b21_original_time_map_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:13:06.570236+00:00
-- url     : https://prove2.me/theorems/b6ce6b12-e89e-4e9a-9bb5-1695a236a74e
-- title:
--   Exact original physical compensator time-measure transport
-- statement:
--   The original compensator uses Lebesgue measure restricted to the closed physical time horizon, pushed forward by the real-to-nonnegative-time map. Under the exact almost-everywhere strong measurability condition, its Bochner integral is the real-time set integral of the pulled-back kernel. This reconciles the two time measures without altering the terminal or ruin masks.
-- source:
--   Direct measure transport needed for 7ccc2a1a original inclusive K_n-minus-A_n convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_time_map_integral
    (T : ℝ) (f : ℝ≥0 → ℝ)
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) :
    (∫ t : ℝ≥0, f t ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
      ∫ t in Icc (0 : ℝ) T, f (Real.toNNReal t) := by sorry
