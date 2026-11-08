-- Prove2me | solution 1 for levy_foundations_compoundDriverFirstArrivalPos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:03:45.547863+00:00
-- url     : https://prove2.me/submissions/b76ae2b0-95a7-46ba-85d9-f93629a00bf7

import Mathlib
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- The original first-arrival consequence of positive exponential interarrivals. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) :
    ∀ᵐ ω ∂μ, 0 < LevyFoundations.arrival τ 0 ω := by
  filter_upwards [levy_foundations_compoundDriverInterarrivalPositive h hr] with ω hpos
  simpa [LevyFoundations.arrival] using hpos 0
