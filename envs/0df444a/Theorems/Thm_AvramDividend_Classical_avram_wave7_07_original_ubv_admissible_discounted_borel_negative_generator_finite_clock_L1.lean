-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_finite_clock_L1
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_finite_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:56:42.490566+00:00
-- url     : https://prove2.me/theorems/f60dfc02-0b96-44fe-bd48-dd1e463cfc3d
-- title:
--   Original UBV admissible negative-generator Borel L1 with true exponential discount
-- statement:
--   On the exact source process and admissible UBV strategy, extend the proved undiscouted finite predictable-clock L1 negative Borel generator drift to exp(-qt) for q≥0. The original predictable exponential-discount measurable helper supplies measurability, and bounded multiplication preserves integrability. No process, clock or Lévy mark law is changed.
-- source:
--   W7-07 original stopped source-jump integrability bridge for W7-08 discounted Ito-Meyer verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_finite_clock_L1
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) * (∫ z in B, G (p,z) ∂X.ν)) μ := by sorry
