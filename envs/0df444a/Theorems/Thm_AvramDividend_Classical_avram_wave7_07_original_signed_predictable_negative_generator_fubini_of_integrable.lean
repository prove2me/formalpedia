-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
-- name    : AvramDividend.Classical.avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:09:04.94299+00:00
-- url     : https://prove2.me/theorems/b8301790-765b-4e98-9b18-46feb226cfd2
-- title:
--   Original Lévy signed predictable negative Taylor generator drift Fubini under exact product integrability
-- statement:
--   For the original spectrally negative Levy process X.X on Ω,P,filtration and its given negative Levy measure X.ν, with exact ruin stopped prepayment C2 Taylor correction and jointly predictable marked thinning S and signed predictable unit coefficient a, prove the Bochner Fubini identity between the integrated source mark correction on the true predictable product μ⊗X.ν|negative and the iterated μ-time negative mark integral. Explicitly require product Integrable for the signed kernel; separate W7-07 finite-energy theorem will discharge it. Uses no replacement jump process or intrinsic count compensation.
-- source:
--   W7-07 exact original-source signed predictable generator Fubini, direct Mathlib integral_prod and source sFinite negative measure; W7-08 consumer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
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
    (Integrable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
      (S.indicator (fun p => a p.1 * HS p)) r) (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       μ.prod (X.ν.restrict (Iio (0 : ℝ))))) →
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      (S.indicator (fun p => a p.1 * HS p)) r ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       μ.prod (X.ν.restrict (Iio (0 : ℝ))))) = (∫ p : ℝ≥0 × Ω, a p *
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∂μ) := by sorry
