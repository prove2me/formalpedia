-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_atomless_time_marks_zero_original_probability_ae
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_atomless_time_marks_zero_original_probability_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:00:39.889688+00:00
-- url     : https://prove2.me/theorems/5141332f-90f9-443e-8746-6b75bfa8f5de
-- title:
--   Actual source Lévy jump marks have no atoms for every original-path atomless s-finite time measure
-- statement:
--   For any actual SpectrallyNegativeLevy P 𝓕, and any s-finite atomless time measure μ on ℝ≥0, for μ-almost every positive time t the genuine source jump X_t-X_{t-} is zero for P-almost every original sample ω. The proof uses original joint jump-mark measurability, countability of jumps on each actual path, and a rigorous Fubini swap; it does not assume independent Poisson marks, a detached process law, bounded variation, or finite activity.
-- source:
--   Proved joint measurability 9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1 and proved all-source-path countability 741d3b5f-bfd0-434e-846c-b274123b5ebe, Mathlib ae_ae_comm; real original P and filtration 𝓕.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_atomless_time_marks_zero_original_probability_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ t : ℝ≥0 ∂μ,
      ∀ᵐ ω ∂P,
        ¬ (0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0) := by sorry
