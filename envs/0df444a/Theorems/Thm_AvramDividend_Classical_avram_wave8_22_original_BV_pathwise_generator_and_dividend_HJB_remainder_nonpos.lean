-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:28:17.297026+00:00
-- url     : https://prove2.me/theorems/7c09dd19-8d1a-44f5-b3d0-6e5279e07d47
-- title:
--   Actual BV pathwise finite-horizon physical generator plus original dividend Stieltjes HJB remainder is nonpositive
-- statement:
--   For the original bounded variation spectrally negative Levy process and admissible dividend path, the discounted physical drift plus genuine negative mark generator integral, integrated over an arbitrary measurable strictly interior time region of the physical finite time clock, plus the original discounted Stieltjes dividend gradient correction over an arbitrary strictly interior physical payment region, is nonpositive on every original sample path. This packages the proved exact BV physical generator HJB sign and original dividend Stieltjes sign into the precise remainder needed for W8-04's stopped C1 budget, without stochastic Ito or assumed zero mean.
-- source:
--   Proved W7-02 actual physical generator discounted envelope a0879a2f-f3fc-40f0-82e3-d460355c444b and Proved original physical dividend Stieltjes nonpositivity f2c20057-64e1-4c84-afe6-7003b7e2912b. No new jump-measure source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
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
  (hRegion : ∀ ω t, t ∈ A ω →
    0 < Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧ ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
  (hGInt : ∀ ω, IntegrableOn
    (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) (A ω) (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (B : Ω → Set ℝ) (hBm : ∀ ω, MeasurableSet (B ω))
  (hDivRegion : ∀ ω s, s ∈ B ω →
    0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
  (hDivInt : ∀ ω, IntegrableOn
    (fun s : ℝ => Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω))) (B ω) (dividendMeasure D ω))
  (Gdrift Hdiv : Ω → ℝ)
  (hGDef : ∀ ω, Gdrift ω = ∫ t in A ω, Real.exp (-(q * (t : ℝ))) * (X.drift * deriv w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + (∫ z in Iio (0 : ℝ), w ((Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) + z) - w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) - q * w (Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (hHDef : ∀ ω, Hdiv ω = ∫ s in B ω, Real.exp (-(q * s)) * (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂(dividendMeasure D ω)) :
  ∀ ω, Gdrift ω + Hdiv ω ≤ 0 := by sorry
