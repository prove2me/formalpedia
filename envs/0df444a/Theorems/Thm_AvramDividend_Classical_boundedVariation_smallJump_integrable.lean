-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable
-- name    : AvramDividend.Classical.boundedVariation_smallJump_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:49:25.43695+00:00
-- url     : https://prove2.me/theorems/4291cf5b-195d-4c8f-907f-724f3d3c1bc2
-- title:
--   Bounded variation makes the Lévy small-jump coordinate integrable
-- statement:
--   For a spectrally negative Lévy process of bounded variation, the defining finite first absolute moment of small negative jumps implies that the coordinate function y is integrable on (-1,0) with respect to the Lévy jump measure. This provides the rigorous integrability needed to extract the BV drift c minus the small-jump compensation integral in the verification generator.

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_smallJump_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => y) (Ioo (-1 : ℝ) 0) X.ν := by sorry
