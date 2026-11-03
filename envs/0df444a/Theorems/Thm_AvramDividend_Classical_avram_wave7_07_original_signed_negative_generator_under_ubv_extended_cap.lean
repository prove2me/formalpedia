-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_negative_generator_under_ubv_extended_cap
-- name    : AvramDividend.Classical.avram_wave7_07_original_signed_negative_generator_under_ubv_extended_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:46:34.806594+00:00
-- url     : https://prove2.me/theorems/cd43f52c-b457-468c-8fc4-877f5f5a30ba
-- title:
--   Original stopped signed predictable negative Lévy generator compensation under UBV extended cap
-- statement:
--   For the actual source process X and right-continuous predictable sigma algebra, signed unit predictable time weights and jointly measurable mark thinnings preserve the exact negative compensated Taylor product-to-generator identity under the corrected UBV C² hypothesis below an extended-real cap C. The helper bridges that hypothesis to any finite localisation R with ENNReal.ofReal R<C.
-- source:
--   W7-07 actual source negative jump generator identity handed to W7-08 stopped Itô–Meyer residual; all source objects unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_stopped_negative_taylor_product_eq_generator_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_extended_cap_local_C2_restrict

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_signed_negative_generator_under_ubv_extended_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (R u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < R)
    (hRcap : ENNReal.ofReal R < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, |a p| ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      (S.indicator (fun p => a p.1 * HS p)) r ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) = (∫ p : ℝ≥0 × Ω,
      a p * (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) ∂μ) := by sorry
