-- Prove2me | solution 1 for levy_foundations_isInfinitelyDivisibleLaw_iff_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:31:01.891734+00:00
-- url     : https://prove2.me/submissions/9beab93c-9864-4cd4-9973-1730ce980d88

import Mathlib
import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Theorems.Thm_levy_foundations_iteratedConvolutionPower_eq_realConv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution (μ : Measure ℝ) :
    LevyFoundations.isInfinitelyDivisibleLaw μ ↔
      LevyFoundations.isInfinitelyDivisible μ := by
  simp only [LevyFoundations.isInfinitelyDivisibleLaw,
    LevyFoundations.isInfinitelyDivisible,
    levy_foundations_iteratedConvolutionPower_eq_realConv]
