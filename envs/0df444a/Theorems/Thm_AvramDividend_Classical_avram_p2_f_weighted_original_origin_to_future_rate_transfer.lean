-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_to_future_rate_transfer
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_origin_to_future_rate_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:25:22.412089+00:00
-- url     : https://prove2.me/theorems/09e8f463-9bac-4657-a83f-852260ccbc9e
-- title:
--   Transfer a separately established original zero-origin jump mean to arbitrary adapted ENNReal weights and shifted rectangles
-- statement:
--   If the exact original intrinsic marked jump count on (0,T] for a measurable Borel mark set B has mean r, then for the unchanged original Lévy process the count on (s,s+T] weighted by any nonnegative source-past-measurable ENNReal H has expectation E[H]*r. This is a conditional bridge, not an unconditional ν-rate statement. To obtain W7-06 instantiate r=(T:ENNReal)*X.ν B only after P2-A proves the independent original zero-origin rate. The result handles unbounded weights and ENNReal 0*∞ without division or finite expectation hypotheses.
-- source:
--   Exact W7-06 adapted weighted target d27347c9, established original future measurable extractor 5cf3e058, original arbitrary future past-weight factor 8a788cbd, and stationary source count mean add050a6. The rate is a genuine explicit hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_origin_to_future_rate_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (r : ℝ≥0∞)
    (hOrigin : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = r) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * r := by sorry
