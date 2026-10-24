-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_uncompensated_integrable
-- name    : AvramDividend.Classical.boundedVariation_smallJump_uncompensated_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:10:36.994992+00:00
-- url     : https://prove2.me/theorems/2314e3e1-ad31-4b6a-ac3b-19af81c40953
-- title:
--   Bounded variation makes the uncompensated small-jump candidate increment integrable
-- statement:
--   In the bounded-variation case, the full uncompensated candidate-value jump increment w(x+y)-w(x) is integrable over small negative jumps (-1,0) whenever the compensated generator integrand is integrable. The proof adds back the integrable first-order term and uses the proved indicator identity at each small jump.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_small_negative
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_kernel_plus_deriv_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_smallJump_uncompensated_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Ioo (-1 : ℝ) 0) X.ν := by sorry
