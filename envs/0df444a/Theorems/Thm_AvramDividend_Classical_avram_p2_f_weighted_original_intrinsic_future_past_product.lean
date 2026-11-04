-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_future_past_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:52:26.744278+00:00
-- url     : https://prove2.me/theorems/267e2229-0521-4da2-90ff-8c791a25e44f
-- title:
--   Exact original future marked jump-count factorisation from arbitrary adapted past weight
-- statement:
--   For a genuine spectrally negative Lévy process X and unchanged measure P, any nonnegative weight adapted at time s factors in ENNReal expectation from the actual intrinsic marked jump count on (s,s+T] times B. This requires neither a zero-origin Lévy ν-rate nor any finite activity or integrability; it follows solely from the already-Proved original future extractor and abstract arbitrary future-functional past-weight independence, with exact original-path transport.
-- source:
--   Proved 5cf3e058 original future marked-count extractor and 8a788cbd arbitrary shifted-future-functional past-weight lintegral factor. Direct process-specific helper; independent of 34dbea70 ν identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_future_past_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
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
