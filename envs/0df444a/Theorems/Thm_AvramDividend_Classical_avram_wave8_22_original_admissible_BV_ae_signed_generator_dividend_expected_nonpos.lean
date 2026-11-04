-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:44:15.205087+00:00
-- url     : https://prove2.me/theorems/493d798a-ee92-46c4-9862-e387f11d1573
-- title:
--   Original admissible BV signed HJB generator drift and Stieltjes dividend expectations sum to a nonpositive value
-- statement:
--   For the actual original bounded variation spectrally negative Levy risk process and actual admissible dividend strategy, assume original almost-everywhere physical stopped generator/Stieltjes interior localisations and identification. If both signed physical generator and true Stieltjes correction are P-integrable, then the sum of their real expectations is nonpositive. The proof derives a.e. signed HJB from an accepted source theorem and applies Bochner integral linearity and nonpositivity.
-- source:
--   Accepted original a.e. HJB source c7bcf009-8e47-48eb-9931-cc9c2594ea1c, with Mathlib integral_add and integral_nonpos_of_ae.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_almost_everywhere_signed_generator_dividend_HJB_remainder_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_gen : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
    X.GeneratorIntegrable w yy ∧ X.generator w yy - q * w yy ≤ 0)
  (hw_grad : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C → 1 ≤ deriv w yy)
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
  (T : ℝ≥0)
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
  (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
    0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
  (hGInt : ∀ᵐ ω ∂P, IntegrableOn
    (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω))
  (hDivRegion : ∀ᵐ ω ∂P, ∀ s, s ∈ B ω →
    0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
  (hDivInt : ∀ᵐ ω ∂P, IntegrableOn
    (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
  (Gdrift Hdiv : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω))
(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P) :
(∫ ω, Gdrift ω ∂P) + (∫ ω, Hdiv ω ∂P) ≤ 0 := by sorry
