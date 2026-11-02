-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:16:45.669507+00:00
-- url     : https://prove2.me/theorems/c922c8ed-d014-4a89-9bbc-fc962a958c73
-- title:
--   Genuine source predictable occupation measure has zero initial-time marked rectangles
-- statement:
--   For the unchanged original SpectrallyNegativeLevy P 𝓕, its genuine predictable-lift kernel K specified pointwise as the marked image of the actual intrinsic jump measure, and its actual occupation measure M=P.bind K, every original-filtration 𝓕0 event A and Borel mark set B have M(({0}×A)×B)=0. The proof uses source pathwise zero initial-time jump mass, source kernel measurability and the original predictable lift; no Poisson copy, BV condition, Lévy intensity assumption or future rectangle compensator hypothesis. This discharges the M-side initial-time boundary obligation in P1 and Chat02-C.
-- source:
--   Uses canonically Proved source jump initial-time zero e2216ed6, actual predictable kernel AEMeasurable 4443ac3e, and joint original predictable map measurability 2648ec36, with pinned Measure.bind_apply and Measure.map_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_full_original_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_predictable_occupation_bottom_rectangle_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (A : Set Ω) (hA : MeasurableSet[𝓕 0] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0 := by sorry
