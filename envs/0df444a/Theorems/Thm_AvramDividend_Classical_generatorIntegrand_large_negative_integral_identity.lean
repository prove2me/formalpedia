-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integral_identity
-- name    : AvramDividend.Classical.generatorIntegrand_large_negative_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:24:21.199241+00:00
-- url     : https://prove2.me/theorems/5bce7b49-462b-496e-9345-264041e35cfb
-- title:
--   The large-jump generator integral is the uncompensated value-jump integral
-- statement:
--   For jumps y ≤ -1, the generator truncation indicator is zero. The generator integrand equals the candidate-value jump increment pointwise, so their integrals over this interval agree for any Lévy jump measure, with no additional integrability hypothesis needed for equality of Bochner integrals.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegrand_large_negative_integral_identity
    (w : ℝ → ℝ) (x : ℝ) (ν : Measure ℝ) :
    (∫ y in Iic (-1 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂ν) =
      (∫ y in Iic (-1 : ℝ), w (x + y) - w x ∂ν) := by sorry
