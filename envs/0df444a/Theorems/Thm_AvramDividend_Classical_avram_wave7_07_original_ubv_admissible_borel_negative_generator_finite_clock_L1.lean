-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
-- name    : AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:51:12.632791+00:00
-- url     : https://prove2.me/theorems/d587cbe0-4eca-4c45-80da-d67b0de53b18
-- title:
--   Original UBV admissible strategy has finite predictable-clock Borel negative-generator L1 under an extended cap
-- statement:
--   Take the exact original W7-08 IsAdmissibleLe and extended-real C² smoothness hypotheses. Localise the positive reserve band below the extended cap to obtain a finite real R and ContDiffOn on (0,R), use hD.1.1 for the original IsDividendStrategy, and apply the already Proved original Borel negative-generator finite predictable-clock L¹ theorem. The actual source X.X, ν, ruin time and compensation convention are unchanged.
-- source:
--   W7-07 admissible original UBV L1 generator integrability bridge for W7-08 stopped Itô verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
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
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in B, G (p,z) ∂X.ν) μ := by sorry
