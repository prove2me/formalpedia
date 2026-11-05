-- Prove2me | solution 1 for levy_foundations_weakCharFunTightness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:50:53.506263+00:00
-- url     : https://prove2.me/submissions/be31d956-b85b-4c55-87eb-4821524527ad

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Definitions.Def_levy_foundations_probabilityCharacteristicFun
import Definitions.Def_levy_foundations_weakCharFunTendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-! Tightness from pointwise convergence of characteristic functions. -/
theorem solution
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : LevyFoundations.weakCharFunTendsto μs atTop μ) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure ℝ))) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure (μs n : Measure ℝ) :=
    fun n => inferInstance
  have hcont : ContinuousAt (fun t : ℝ => charFun (μ : Measure ℝ) t) 0 :=
    MeasureTheory.continuous_charFun.continuousAt
  exact MeasureTheory.isTightMeasureSet_of_tendsto_charFun hcont h
