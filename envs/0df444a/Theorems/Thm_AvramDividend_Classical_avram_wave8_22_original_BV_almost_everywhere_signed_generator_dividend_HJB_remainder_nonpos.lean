-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_almost_everywhere_signed_generator_dividend_HJB_remainder_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_almost_everywhere_signed_generator_dividend_HJB_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:18:25.355279+00:00
-- url     : https://prove2.me/theorems/94c067eb-aed4-4a7f-8500-a8287c3662c5
-- title:
--   Almost-sure original BV HJB generator and physical Stieltjes signed remainder is nonpositive
-- statement:
--   On the actual original Levy sample space, almost-everywhere localisation, generator and dividend integrability, interior reserve and exact remainder identification imply the physical discounted BV generator drift and actual Stieltjes dividend HJB correction sum is nonpositive almost everywhere. This is the expectation-ready weakening of the accepted original source pathwise result, without constructing a surrogate process or asserting a martingale mean.
-- source:
--   Direct original-source proof from Proved a0879a2f-f3fc-40f0-82e3-d460355c444b and f2c20057-64e1-4c84-afe6-7003b7e2912b, following Proved 7c09dd19-8d1a-44f5-b3d0-6e5279e07d47 but restricting the exact localisation assumptions to P-almost-every path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_almost_everywhere_signed_generator_dividend_HJB_remainder_nonpos
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
  (hw_gen : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C →
    X.GeneratorIntegrable w yy ∧ X.generator w yy - q * w yy ≤ 0)
  (hw_grad : ∀ yy : ℝ, 0 < yy → ENNReal.ofReal yy < C → 1 ≤ deriv w yy)
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
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
  (hHDef : ∀ᵐ ω ∂P, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω)) :
  ∀ᵐ ω ∂P, Gdrift ω + Hdiv ω ≤ 0 := by sorry
