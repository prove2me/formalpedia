-- Prove2me | solution 1 for levy_foundations_isInfinitelyDivisible_iff_leanlevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:08:14.498359+00:00
-- url     : https://prove2.me/submissions/ebc4c930-33ea-4cee-afa7-3b1c2b536b31

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- The two convolution-power definitions satisfy the same recursion. -/
private theorem iteratedConv_eq_source (ν : Measure ℝ) (n : ℕ) :
    LevyFoundations.iteratedConv ν n = ν.iteratedConv n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ν ∗ LevyFoundations.iteratedConv ν n = ν ∗ ν.iteratedConv n
    rw [ih]

/-- The two notions of infinite divisibility agree via convolution powers. -/
theorem solution (μ : Measure ℝ) :
    LevyFoundations.isInfinitelyDivisible μ ↔ ProbabilityTheory.IsInfinitelyDivisible μ := by
  constructor
  · intro h n hn
    obtain ⟨ν, hν, heq⟩ := h n hn
    refine ⟨ν, hν, ?_⟩
    simpa only [iteratedConv_eq_source] using heq
  · intro h n hn
    obtain ⟨ν, hν, heq⟩ := h n hn
    refine ⟨ν, hν, ?_⟩
    simpa only [iteratedConv_eq_source] using heq
