-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_admissible_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
-- name    : AvramDividend.Classical.avram_wave8_22_original_admissible_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:15:56.484064+00:00
-- url     : https://prove2.me/theorems/d1a7ddbe-3c6e-4dd8-833e-84c65c86d4df
-- title:
--   Original admissible BV dividend strategy has nonpositive physical generator and Stieltjes HJB remainder
-- statement:
--   The original bounded-variation spectrally negative Levy risk process and actual IsAdmissibleLe dividend strategy directly yield the pathwise nonpositive signed discounted generator and original Stieltjes dividend HJB sum. The actual admissibility structure supplies IsDividendStrategy; no additional strategy premise is required. This reuses the genuinely Proved original physical lemma and retains all interior and integrability hypotheses.
-- source:
--   Direct corollary of Proved 7c09dd19-8d1a-44f5-b3d0-6e5279e07d47; IsAdmissibleLe X x C D has a proof of IsDividendStrategy 𝓕 D as hD.1.1.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_admissible_BV_pathwise_generator_and_dividend_HJB_remainder_nonpos
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
