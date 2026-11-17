-- Prove2me | solution 1 for leftClosedInfinite_mem_borelAlgebraReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:30:29.479207+00:00
-- url     : https://prove2.me/submissions/3df33fbe-1189-4fa8-8ac5-f865a50aada2

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Theorems.Thm_closedInterval_mem_borelAlgebraReal
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_borelAlgebraReal_eq_borel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution (b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Iic b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Iic
