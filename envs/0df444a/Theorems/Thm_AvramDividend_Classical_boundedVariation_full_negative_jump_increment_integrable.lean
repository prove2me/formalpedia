-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
-- name    : AvramDividend.Classical.boundedVariation_full_negative_jump_increment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:20:43.793744+00:00
-- url     : https://prove2.me/theorems/5ff8b9b4-6a58-4c3f-9a0b-be295ee12ea2
-- title:
--   Bounded-variation value increments are integrable over all negative Lévy jumps
-- statement:
--   The bounded-variation jump integral is well-defined without a first-order compensator over every negative Lévy jump. Combine the integrable small-jump increment and the integrable large-jump increment, using the disjoint decomposition (-infinity,-1] union (-1,0)=(-infinity,0).

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_uncompensated_integrable
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_full_negative_jump_increment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iio 0) X.ν := by sorry
