-- Prove2me | solution 1 for levy_foundations_iteratedConvolutionPower_eq_realConv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:25:28.073241+00:00
-- url     : https://prove2.me/submissions/f0030df9-b0fb-4461-beb7-f6479bf29034

import Mathlib
import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Definitions.Def_levy_foundations_iteratedConv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution (μ : Measure ℝ) (n : ℕ) :
    LevyFoundations.iteratedConvolutionPower μ n =
      LevyFoundations.iteratedConv μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change μ ∗ LevyFoundations.iteratedConvolutionPower μ n =
        μ ∗ LevyFoundations.iteratedConv μ n
      rw [ih]
