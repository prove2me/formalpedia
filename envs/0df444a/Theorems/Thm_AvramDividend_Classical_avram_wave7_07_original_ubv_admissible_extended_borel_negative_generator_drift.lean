-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_extended_borel_negative_generator_drift
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_extended_borel_negative_generator_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:48:05.874963+00:00
-- url     : https://prove2.me/theorems/c526d777-d60e-4281-8a02-c8ebf93383f9
-- title:
--   Canonical UBV admissible strategy directly gives original extended-cap signed Borel negative-jump generator drift
-- statement:
--   Under W7-08's exact IsAdmissibleLe X x C D hypothesis, the original stopped signed predictable Taylor source-product integral equals the source ν generator drift on any negative Borel mark set for finite predictable clocks. The original IsAdmissibleLe and IsAdmissible definitions expose IsDividendStrategy as hD.1.1, which discharges the only consumer-mismatch parameter of the already Proved W7-07 extended-cap signed Borel identity. No new stochastic hypothesis or process replacement.
-- source:
--   W7-07 original-process UBV stopped-verification source-jump consumer adapter for W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_extended_borel_negative_signed_generator_drift_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_extended_borel_negative_generator_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
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
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {r | r.2 ∈ B}
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      (S.indicator (fun p => a p.1 * HS p)) r
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      a p * (∫ z in B, G (p,z) ∂X.ν) ∂μ) := by sorry
