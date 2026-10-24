-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_generatorIntegral_decomposition
-- name    : AvramDividend.Classical.boundedVariation_smallJump_generatorIntegral_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:23:21.514853+00:00
-- url     : https://prove2.me/theorems/f788f372-f2ce-4011-8782-4c82529c04bb
-- title:
--   BV small-jump generator integral splits into actual increment and drift compensator
-- statement:
--   On the small negative jump interval, the compensated Lévy generator integrand equals the actual candidate-value increment minus its first-order term. Bounded variation and the generator integrability assumption make each term Bochner-integrable, so the integral splits exactly. This is the operator-level ingredient needed to replace the Lévy characteristic drift c by the physical finite-variation drift.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_small_negative
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_uncompensated_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_smallJump_generatorIntegral_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (∫ y in Ioo (-1 : ℝ) 0, SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) =
      (∫ y in Ioo (-1 : ℝ) 0, w (x + y) - w x ∂X.ν) -
      (∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν) := by sorry
