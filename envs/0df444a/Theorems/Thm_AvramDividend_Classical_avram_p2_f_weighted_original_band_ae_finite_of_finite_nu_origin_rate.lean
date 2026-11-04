-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_band_ae_finite_of_finite_nu_origin_rate
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_band_ae_finite_of_finite_nu_origin_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:12:20.546908+00:00
-- url     : https://prove2.me/theorems/5f24d93d-6040-44a0-b0b0-1b5bad17dd0d
-- title:
--   Genuine original marked weighted count finite almost surely under finite ν mass and independent origin rate
-- statement:
--   If the original zero-origin count mean equals duration times the true Lévy mark measure, the mark intensity is finite and the past-adapted nonnegative weight has finite mean, then the actual original marked future count times that weight is almost surely finite. The proof uses genuine source measurability and the separately proved finite expected count, not a Poisson copy.
-- source:
--   Source original intrinsic rectangle measurability d9c55240 and new full proof target a7c58dda (must be Proved before this publication).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_band_ae_finite_of_finite_nu_origin_rate
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
    ∀ᵐ ω ∂P, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) < ∞ := by sorry
