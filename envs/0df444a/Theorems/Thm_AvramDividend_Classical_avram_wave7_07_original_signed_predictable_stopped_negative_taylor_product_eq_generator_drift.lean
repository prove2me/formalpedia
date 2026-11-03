-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_stopped_negative_taylor_product_eq_generator_drift
-- name    : AvramDividend.Classical.avram_wave7_07_original_signed_predictable_stopped_negative_taylor_product_eq_generator_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:24:21.610001+00:00
-- url     : https://prove2.me/theorems/d97e1379-e63f-4042-8cfc-8697b9b258c3
-- title:
--   Original process stopped nonlinear negative Taylor source product equals signed generator drift
-- statement:
--   For actual spectrally negative Lévy source X, original stopped controlled reserve Y, dividend strategy D, C2 test w, predictable clock μ, jointly predictable marked S and signed predictable unit coefficient a, prove exact compensated negative-jump Taylor product integral equals finite source generator drift with truncation 1_{-1<z<0}. No Poisson substitution, same Ω,P,filtration,X.ν,ruinTime and prepayment reserve.
-- source:
--   W7-07 bridge combining source product L1, true-source Bochner Fubini and signed generator kernel identification; W7-08 consumer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_signed_predictable_stopped_negative_taylor_product_eq_generator_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
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
