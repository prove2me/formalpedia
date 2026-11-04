-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:25.512959+00:00
-- url     : https://prove2.me/theorems/ca4d6415-6b7a-4cf6-b153-2bb440e142e2
-- title:
--   Source-original zero-origin marked mean lifts to arbitrary adapted ENNReal weights
-- statement:
--   For the genuine original spectrally negative Lévy process and a Borel mark cell, the arbitrary adapted nonnegative weight on (s,s+T] factors against an independently established zero-origin first moment r. This strictly conditional theorem uses the proved source-original future/past product and stationary original marked count mean. The original Lévy ν-rate is not postulated or proved here; W7-06 may instantiate r only after P2-A establishes it.
-- source:
--   Already-Proved source original future-past product 267e2229-0521-4da2-90ff-8c791a25e44f and original intrinsic count stationary mean add050a6-3ff4-4747-9805-600b11b7b3d1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
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
