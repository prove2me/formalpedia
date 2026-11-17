-- Prove2me | solution 1 for thm_2_7_openInterval_mem_generateFrom_strictClosed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:07:51.446468+00:00
-- url     : https://prove2.me/submissions/8c89ea00-add3-40bb-90a7-8e0ab38226d6

import Theorems.Thm_thm_2_7_closedApprox_mem_generateFrom_strictClosed
import Theorems.Thm_thm_2_7_iUnion_closedApprox_eq_Ioo
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution
    {a b : ℝ} (hab : a < b) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (Set.Ioo a b) := by
  rw [← thm_2_7_iUnion_closedApprox_eq_Ioo hab]
  exact MeasurableSet.iUnion
    (fun n => thm_2_7_closedApprox_mem_generateFrom_strictClosed a b n)
