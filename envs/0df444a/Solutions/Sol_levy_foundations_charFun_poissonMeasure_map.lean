-- Prove2me | solution 1 for levy_foundations_charFun_poissonMeasure_map
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T00:28:00.365378+00:00
-- url     : https://prove2.me/submissions/b1b475e3-2a8c-4da8-b3b8-582d4e62aab6

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal Nat

theorem solution (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
      cexp (r * (cexp (ξ * I) - 1)) :=
  charFun_map_cast_poissonMeasure r ξ
