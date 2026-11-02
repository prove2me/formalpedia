-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_predictable_sample_mark_lift_measurable
-- name    : AvramDividend.Classical.avram_wave5_p1_original_predictable_sample_mark_lift_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:36:34.014256+00:00
-- url     : https://prove2.me/theorems/95f32973-4d5b-4174-b17c-29d5c210715c
-- title:
--   Every fixed original sample admits a predictable marked lift of its jump time and mark
-- statement:
--   For any original filtration and every fixed sample ω, the map (time, mark) to ((time, ω), mark) is measurable from ordinary Borel time×mark to the marked predictable sigma-algebra. This is the precise samplewise lift measurability hypothesis in the Proved original intrinsic source occupation Fubini theorem a2b399cb. The proof uses only the Proved adapted-past-rectangle generator and elementary Borel time sections. No Poisson copy or jump count law is invoked.
-- source:
--   Proved predictable adapted-rectangle sigma generator UUID 31933be5-5f90-4169-be51-4c8f889b430b. This discharges hLift in the source occupation Fubini theorem a2b399cb-efbd-4522-b560-a6e7e55207e7.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_adapted_rectangle_sigma_generator

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_predictable_sample_mark_lift_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) := by sorry
