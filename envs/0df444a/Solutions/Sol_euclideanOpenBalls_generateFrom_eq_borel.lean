-- Prove2me | solution 1 for euclideanOpenBalls_generateFrom_eq_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:52:20.015904+00:00
-- url     : https://prove2.me/submissions/c3d06720-92f6-41c9-9c12-4df0c4e87d0b

import Theorems.Thm_metricOpenBalls_isTopologicalBasis
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace
open scoped Pointwise

theorem solution (d : ℕ) :
    MeasurableSpace.generateFrom (euclideanOpenBalls d) =
      borel (EuclideanSpace ℝ (Fin d)) := by
  simpa [euclideanOpenBalls] using
    (metricOpenBalls_isTopologicalBasis
      (α := EuclideanSpace ℝ (Fin d))).borel_eq_generateFrom.symm
