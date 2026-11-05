-- Prove2me | solution 1 for levy_foundations_weakCharFunTendstoToWeak
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:38:13.523445+00:00
-- url     : https://prove2.me/submissions/0c1e12fc-cfa5-4e13-9993-b37ca783e609

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Definitions.Def_levy_foundations_probabilityCharacteristicFun
import Definitions.Def_levy_foundations_weakCharFunTendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-! Lévy's continuity theorem for the mission's characteristic-convergence definition. -/
theorem solution
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : LevyFoundations.weakCharFunTendsto μs atTop μ) :
    Tendsto μs atTop (𝓝 μ) := by
  exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2 h
