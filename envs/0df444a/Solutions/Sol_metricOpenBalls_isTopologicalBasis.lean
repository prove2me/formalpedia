-- Prove2me | solution 1 for metricOpenBalls_isTopologicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:51.420718+00:00
-- url     : https://prove2.me/submissions/fe971284-78b1-48fe-a243-33419d77e1a4

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_coordinateOpenBoxes_eq_openBoxes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace
open scoped Pointwise

theorem solution {α : Type*} [PseudoMetricSpace α] :
    TopologicalSpace.IsTopologicalBasis
      {S : Set α | ∃ c : α, ∃ r : ℝ, 0 < r ∧ S = Metric.ball c r} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro S ⟨c, r, _hr, rfl⟩
    exact Metric.isOpen_ball
  · intro x U hx hU
    rcases Metric.isOpen_iff.mp hU x hx with ⟨r, hr, hsub⟩
    exact ⟨Metric.ball x r, ⟨x, r, hr, rfl⟩, Metric.mem_ball_self hr, hsub⟩
