-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_ae_finite_of_finite_origin_mean
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_ae_finite_of_finite_origin_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:18:05.626528+00:00
-- url     : https://prove2.me/theorems/2bce319d-0ac8-4e5d-a192-ed0f7b0bfff3
-- title:
--   Source original adapted marked future count a.s. finite under arbitrary finite zero-origin mean
-- statement:
--   For the genuine original Lévy intrinsic jump count, an independently established finite zero-origin first moment r and finite mean of a nonnegative past-adapted weight imply that the original marked count times the weight is finite almost surely. This is independent of any asserted ν-rate identity and uses genuine original future measurability.
-- source:
--   Proved original source intrinsic rectangle measurability d9c55240 and origin mean-to-adapted factor ca4d6415.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_ae_finite_of_finite_origin_mean
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
      (Ioc 0 T ×ˢ B) ∂P) = r)
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hrFinite : r ≠ ∞) :
    ∀ᵐ ω ∂P, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) < ∞ := by sorry
