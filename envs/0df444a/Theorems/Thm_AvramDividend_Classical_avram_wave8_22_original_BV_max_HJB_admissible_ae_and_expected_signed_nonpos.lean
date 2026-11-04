-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_max_HJB_admissible_ae_and_expected_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_admissible_ae_and_expected_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:54:24.91444+00:00
-- url     : https://prove2.me/theorems/36dc1874-c8f3-428c-8603-cf21dda2da23
-- title:
--   Original BV maximum HJB entails almost-sure and nonpositive expected physical generator and Stieltjes dividend signed remainder
-- statement:
--   For the original actual Levy risk process with bounded variation and admissible dividend strategy, the original maximum-form generator HJB equation automatically yields both generator and derivative sign conditions. On genuine almost-everywhere interior and integrable original physical generator and dividend Stieltjes regions, the signed remainder is nonpositive P-almost surely and its expected value is nonpositive.
-- source:
--   Accepted c7bcf009 original a.e physical BV HJB; accepted 493d798a original expected HJB; Mathlib le_max_left, le_max_right, linarith.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_HJB_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_ae_signed_generator_dividend_expected_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_max_HJB_admissible_ae_and_expected_signed_nonpos {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw_hjb : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
X.GeneratorIntegrable w yy ∧ max (X.generator w yy - q * w yy) (1 - deriv w yy) = 0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(T : ℝ≥0) (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω)) (hRegion : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω →
0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) (hGInt : ∀ᵐ ω ∂P, IntegrableOn (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
(B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω)) (hDivRegion : ∀ᵐ ω ∂P, ∀ s, s ∈ B ω → 0 < riskProcess X x D s.toNNReal ω ∧
ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C) (hDivInt : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
(Gdrift Hdiv : Ω → ℝ) (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω))
(hGI : Integrable Gdrift P) (hHI : Integrable Hdiv P) :
(∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) + (∫ ω, Hdiv ω ∂P) ≤ 0 := by sorry
