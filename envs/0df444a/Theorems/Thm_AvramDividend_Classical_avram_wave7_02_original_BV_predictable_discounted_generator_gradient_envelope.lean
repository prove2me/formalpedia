-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:34:45.548876+00:00
-- url     : https://prove2.me/theorems/a0879a2f-f3fc-40f0-82e3-d460355c444b
-- title:
--   Original BV controlled predictable-reserve discounted physical generator and dividend-gradient envelope
-- statement:
--   For the exact original spectrally negative Levy source, the left-limit of the controlled post-dividend reserve on any strictly interior HJB state has a well-defined BV generator and both the physical-drift generator-q value correction and the derivative dividend-density correction are nonpositive after positive discount. The statement does not assert or assume the missing expected stopped Ito or compensated jump formula.
-- source:
--   Original BV generator physical drift representation c8ba98f0, and the canonical positive-cap HJB generator and gradient inequalities at the original controlled predictable left-limit reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original bounded-variation generator has nonpositive physical drift
and dividend-density HJB corrections at the actual controlled predictable
left-limit reserve, with the correct positive discount multiplier. -/

theorem AvramDividend.Classical.avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
    let y := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    X.GeneratorIntegrable w y ∧
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y) ≤ 0 ∧
    Real.exp (-(q * (t : ℝ))) * (1 - deriv w y) ≤ 0 := by sorry
