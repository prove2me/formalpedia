-- Prove2me | solution 1 for levy_foundations_compoundDriverArrivalStrictMono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:05:51.168072+00:00
-- url     : https://prove2.me/submissions/f6b4f8d0-55ec-4227-8944-72e296982aaa

import Mathlib
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Positive interarrivals give strictly increasing source arrival times. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) :
    ∀ᵐ ω ∂μ, StrictMono (fun n => LevyFoundations.arrival τ n ω) := by
  filter_upwards [levy_foundations_compoundDriverInterarrivalPositive h hr] with ω hpos
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h_step : LevyFoundations.arrival τ (n + 1) ω =
      LevyFoundations.arrival τ n ω + τ (n + 1) ω := by
    simp [LevyFoundations.arrival, Finset.sum_range_succ]
  rw [h_step]
  exact lt_add_of_pos_right _ (hpos (n + 1))
