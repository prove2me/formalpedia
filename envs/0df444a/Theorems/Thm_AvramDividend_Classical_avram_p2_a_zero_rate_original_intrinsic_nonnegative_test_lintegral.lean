-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:06:44.464434+00:00
-- url     : https://prove2.me/theorems/b1240c2f-450b-42e2-9d77-44956733f73d
-- title:
--   Original Lévy intrinsic jump-measure nonnegative test integral equals the source pathwise marked sum
-- statement:
--   For the original SpectrallyNegativeLevy process on its original sample space, any nonnegative measurable time-mark test integrates against the actual intrinsic restricted count push-forward as the time-indexed sum of jump marks. Measurability follows from the previously established joint jump-mark theorem and original nonzero-jump time-set measurability. No Poisson or compensator law is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_count_restrict_map_test_lintegral

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_intrinsic_nonnegative_test_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (g : ℝ≥0 × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑' u : ℝ≥0,
        ({v : ℝ≥0 | 0 < v ∧
          X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).indicator
          (fun v => g (v, X.X v ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v)) u := by sorry
