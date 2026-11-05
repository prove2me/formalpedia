-- Prove2me | solution 1 for levy_foundations_probability_iteratedConvolutionPower
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:55.214167+00:00
-- url     : https://prove2.me/submissions/514b35f9-a31a-4367-aa54-50299bbf5d95

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory MeasureTheory.Measure

theorem solution
    {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (LevyFoundations.iteratedConvolutionPower μ n) := by
  induction n with
  | zero =>
    show IsProbabilityMeasure (Measure.dirac (0 : E))
    infer_instance
  | succ n ih =>
    show IsProbabilityMeasure (μ ∗ LevyFoundations.iteratedConvolutionPower μ n)
    infer_instance
