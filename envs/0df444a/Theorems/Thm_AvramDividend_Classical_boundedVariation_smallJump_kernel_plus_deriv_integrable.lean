-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_kernel_plus_deriv_integrable
-- name    : AvramDividend.Classical.boundedVariation_smallJump_kernel_plus_deriv_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:07:07.154369+00:00
-- url     : https://prove2.me/theorems/00a54294-7d04-4ec6-bf70-5b1340e5b89a
-- title:
--   BV small-jump generator kernel plus its derivative compensator is integrable
-- statement:
--   For a bounded-variation Lévy process, integrability of the compensated generator kernel on the negative half-line and integrability of the first-order small-jump compensation imply integrability of their sum on (-1,0). On that interval this sum is the uncompensated candidate value increment w(x+y)-w(x), enabling the BV finite-variation generator to be expressed with its physical drift.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_smallJump_kernel_plus_deriv_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn
      (fun y : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand w x y + deriv w x * y)
      (Ioo (-1 : ℝ) 0) X.ν := by sorry
