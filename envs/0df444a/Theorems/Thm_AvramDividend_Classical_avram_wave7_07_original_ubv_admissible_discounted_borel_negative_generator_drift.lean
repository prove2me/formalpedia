-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_drift
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:53:05.955677+00:00
-- url     : https://prove2.me/theorems/50a98f5e-7acf-4145-95bd-6ba8c2f531d8
-- title:
--   UBV admissible stopped negative-jump Borel source generator drift with genuine predictable exponential discount
-- statement:
--   For the exact original UBV admissible dividend strategy and C² w under extended-real cap C, the stopped nonlinear negative-jump Taylor product weighted by exp(-q t) equals the source Lévy generator drift restricted to any negative Borel mark set on a finite original predictable clock. Positivity q≥0 makes the discount bounded by one, and the proved original predictable exponential-discount helper establishes measurability. The theorem reuses the accepted original admissibility adapter with no altered process or extra stochastic count assumption.
-- source:
--   W7-07 direct discounted source-jump compensation interface under canonical W7-08 hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_extended_borel_negative_generator_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_drift
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
    (q : ℝ) (hq : 0 ≤ q) :
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
      (S.indicator (fun p => Real.exp (-(q * (p.1.1 : ℝ))) * HS p)) r
        ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
          μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) * (∫ z in B, G (p,z) ∂X.ν) ∂μ) := by sorry
