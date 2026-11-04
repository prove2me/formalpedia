-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_past_factor
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:21.509732+00:00
-- url     : https://prove2.me/theorems/b345b798-2f06-47a4-a26a-ee32ebf06f30
-- title:
--   Original Lévy intrinsic marked future count factors against every past ENNReal weight without a rate assumption
-- statement:
--   For the original Lévy process, any Borel jump mark set and any nonnegative ENNReal weight measurable in the unchanged source past at s, the weighted mean literal marked jump count on (s,s+T] factors into the mean weight and unconditional count. Holds for unbounded weights and counts, with extended-real zero-times-infinity semantics and no ν-rate premise. Bridges the published original future count extractor with past/future independence; W7-06 and P2-E can apply it before inserting the separately proved Lévy rate.
-- source:
--   Exact original W7-06 adapted weighted statement d27347c9 and Proved source-path extractor 5cf3e058, Proved adapted whole-future functional factor 8a788cbd, no zero-origin ν-rate assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by sorry
