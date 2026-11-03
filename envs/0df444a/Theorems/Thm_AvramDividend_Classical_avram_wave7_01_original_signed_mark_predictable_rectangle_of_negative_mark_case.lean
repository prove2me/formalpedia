-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_signed_mark_predictable_rectangle_of_negative_mark_case
-- name    : AvramDividend.Classical.avram_wave7_01_original_signed_mark_predictable_rectangle_of_negative_mark_case
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:50:34.709229+00:00
-- url     : https://prove2.me/theorems/72b3e005-26e7-4acd-b2e5-1e7c0935b698
-- title:
--   Actual original arbitrary-mark predictable rectangle follows exactly from its negative-mark instance
-- statement:
--   For the unchanged original SpectrallyNegativeLevy Ω,P,𝓕,X, fixed s≤t, measurable history A and Borel mark B, the negative-mark restriction B∩(-∞,0) compensator identity implies the original arbitrary-mark rectangle identity. The theorem proves the reduction using genuine pathwise original jump support and the structural ν support; no BV or finite activity, proxy process, or conditional compensation conclusion is assumed.
-- source:
--   Proved source negative support 56a5b5da; separately Proved ν support c324380a; Mathlib lintegral_congr over the same past A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_signed_mark_predictable_rectangle_of_negative_mark_case
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg :
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) *
          X.ν (B ∩ Iio (0 : ℝ))) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
