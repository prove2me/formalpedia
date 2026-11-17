-- Prove2me | solution 1 for thm_2_8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:14:31.462728+00:00
-- url     : https://prove2.me/submissions/dd933203-8abd-4cae-a919-e224a9ec1716

import Theorems.Thm_euclideanOpenBox_mem_generateFrom_openBalls
import Theorems.Thm_euclideanOpenBall_mem_generateFrom_openBoxes
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
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
    MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
      borelAlgebraEuclidean d := by
  change MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
    MeasurableSpace.generateFrom (euclideanOpenBalls d)
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun S hS =>
      euclideanOpenBox_mem_generateFrom_openBalls d hS
  · refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨c, r, hr, rfl⟩
    exact euclideanOpenBall_mem_generateFrom_openBoxes d c hr
