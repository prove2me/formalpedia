-- Prove2me | solution 1 for levy_foundations_charFun_iteratedConvolutionPower
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:09:59.311539+00:00
-- url     : https://prove2.me/submissions/b84146c8-7cf9-4975-b66c-96fe2785e8ed

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory MeasureTheory.Measure

theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) (t : E) :
    charFun (LevyFoundations.iteratedConvolutionPower μ n) t =
      (charFun μ t) ^ n := by
  induction n with
  | zero =>
    show charFun (Measure.dirac (0 : E)) t = _
    simp [charFun_dirac]
  | succ n ih =>
    have hp : IsProbabilityMeasure (LevyFoundations.iteratedConvolutionPower μ n) := by
      clear ih
      induction n with
      | zero =>
        show IsProbabilityMeasure (Measure.dirac (0 : E))
        infer_instance
      | succ n ih =>
        show IsProbabilityMeasure (μ ∗ LevyFoundations.iteratedConvolutionPower μ n)
        infer_instance
    show charFun (μ ∗ LevyFoundations.iteratedConvolutionPower μ n) t = _
    rw [charFun_conv, ih, pow_succ, mul_comm]
