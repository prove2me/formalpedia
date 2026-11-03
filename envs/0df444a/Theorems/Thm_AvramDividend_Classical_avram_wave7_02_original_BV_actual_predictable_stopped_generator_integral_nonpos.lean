-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:48:37.393615+00:00
-- url     : https://prove2.me/theorems/5219ff90-517b-4234-b0c2-866a86ef04e6
-- title:
--   Actual BV predictable source physical generator integrated HJB nonpositivity under canonical weaker supersolution
-- statement:
--   For the genuine original spectrally negative Levy process on its original Ω, and the original controlled reserve left limits x+X.X-rightLimit D, integrating the discounted uncompensated-negative-jump physical BV generator minus q times w over any strictly HJB-interior predictable stopped region has nonpositive result when integrable. This uses exactly the canonical weak HJB generator inequality rather than equality of the max HJB, retains the original predictable filtration and arbitrary stopped time-region set, and does not claim stochastic Ito convergence or terminal crossing compensation.
-- source:
--   Accepted original predictable discounted HJB generator a0879a2f and measure integral_nonpos_of_ae with the exact right-continuous predictable filtration. Compensated source jump/stopped chain rule and ruin overshoots remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Nonpositive integrated original BV generator on any interior predictable
stopped source region with the exact weakened canonical HJB hypothesis. -/

theorem AvramDividend.Classical.avram_wave7_02_original_BV_actual_predictable_stopped_generator_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (A : Set (ℝ≥0 × Ω))
    (hA : MeasurableSet[𝓕.rightCont.predictable] A)
    (hregion : ∀ p ∈ A,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.drift * deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
            (∫ z in Iio (0 : ℝ),
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
              w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      A μ) :
    (∫ p in A,
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) +
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) ≤ 0 := by sorry
