-- Prove2me | solution 1 for levy_foundations_fourierConvolutionCharFun
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:28:03.016792+00:00
-- url     : https://prove2.me/submissions/a82aa629-46a2-479d-95f4-7ff053368ce6

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_measureFourier
import Definitions.Def_levy_foundations_probabilityCharacteristicFun

open MeasureTheory Complex ComplexConjugate

lemma poi_measureFourier_eq (μ : FiniteMeasure ℝ) (ξ : ℝ) :
    LevyFoundations.measureFourier μ ξ = charFun (μ : Measure ℝ) ξ := by
  rw [LevyFoundations.measureFourier, charFun_apply]
  simp_rw [Real.inner_apply, mul_comm ξ]

theorem solution
    (μ ν : FiniteMeasure ℝ) (ξ : ℝ) :
    LevyFoundations.measureFourier μ ξ * LevyFoundations.measureFourier ν ξ =
      charFun ((μ : Measure ℝ) ∗ (ν : Measure ℝ)) ξ := by
  rw [charFun_conv, poi_measureFourier_eq, poi_measureFourier_eq]
