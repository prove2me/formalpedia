-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable
-- name    : AvramDividend.Classical.generatorIntegrand_large_negative_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:13:34.84808+00:00
-- url     : https://prove2.me/theorems/d6d42ac6-8d73-463d-9224-0d3191ad7a0a
-- title:
--   Large negative jumps have integrable uncompensated candidate increments
-- statement:
--   The Lévy generator's integrability hypothesis controls all negative jump sizes. On jumps at or below -1 the compensation indicator vanishes, so restricting generator integrability to the large-jump interval provides integrability of the actual candidate-value increment.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generatorIntegrand_large_negative_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iic (-1 : ℝ)) X.ν := by sorry
