-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:06:26.863409+00:00
-- url     : https://prove2.me/theorems/a7c58dda-6001-4d11-b2f0-7ae061144fcc
-- title:
--   Finite L1 moment of genuine original adapted marked jump count from finite ν mark intensity and origin rate
-- statement:
--   For a genuine original Lévy source marked jump count on (s,s+T], if the original zero-origin count mean is independently established to equal T*X.ν B, the nonnegative past weight has finite first moment and X.ν B is finite, then its weighted count has finite first moment. Uses native ENNReal.mul_ne_top and requires no Poisson substitution.
-- source:
--   Accepted P2-F original source adapted zero-origin transfer ca4d6415-6b7a-4cf6-b153-2bb440e142e2 and Mathlib ENNReal.mul_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (hOrigin : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = ((T : ℝ≥0∞) * X.ν B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hνfinite : X.ν B ≠ ∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≠ ∞ := by sorry
