-- Prove2me | solution 1 for levy_foundations_poissonTimeCountAdd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:44:54.367627+00:00
-- url     : https://prove2.me/submissions/118374f0-d8db-460d-b548-7e2ecb72e01b

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_poissonTimeCount
import Theorems.Thm_ProbabilityTheory_poissonTimeCount_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (A : Set E) (s t : ℝ) (hA : MeasurableSet A)
    (h0s : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    LevyFoundations.poissonTimeCount K X A t ω =
      LevyFoundations.poissonTimeCount K X A s ω +
        LevyFoundations.poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A) := by
  change ProbabilityTheory.poissonTimeCount K X A t ω =
    ProbabilityTheory.poissonTimeCount K X A s ω +
      ProbabilityTheory.poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A)
  exact ProbabilityTheory.poissonTimeCount_add hA h0s hst ω
