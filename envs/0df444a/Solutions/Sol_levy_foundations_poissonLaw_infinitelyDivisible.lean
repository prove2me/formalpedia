-- Prove2me | solution 1 for levy_foundations_poissonLaw_infinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:28:04.143985+00:00
-- url     : https://prove2.me/submissions/a22c776d-e800-48aa-96f1-7b47ff9a3664

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex
open scoped NNReal Nat

lemma poi_iter (s : ℝ≥0) (k : ℕ) :
    LevyFoundations.iteratedConvolutionPower ((poissonMeasure s).map (Nat.cast : ℕ → ℝ)) k
      = (poissonMeasure ((k : ℝ≥0) * s)).map (Nat.cast : ℕ → ℝ) := by
  induction k with
  | zero =>
    simp only [LevyFoundations.iteratedConvolutionPower]
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_map_cast_poissonMeasure]
    simp
  | succ k ih =>
    simp only [LevyFoundations.iteratedConvolutionPower]
    rw [ih, map_cast_poissonMeasure_conv]
    congr 2
    push_cast
    ring

theorem solution
    (r : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) := by
  intro n hn
  refine ⟨(poissonMeasure (r / n)).map (Nat.cast : ℕ → ℝ), inferInstance, ?_⟩
  rw [poi_iter]
  congr 2
  have : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
