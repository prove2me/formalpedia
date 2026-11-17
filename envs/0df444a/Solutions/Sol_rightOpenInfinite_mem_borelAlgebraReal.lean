-- Prove2me | solution 1 for rightOpenInfinite_mem_borelAlgebraReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:51:33.343834+00:00
-- url     : https://prove2.me/submissions/d5ac3223-9bcc-4e7e-a2a6-52986a636128

import Theorems.Thm_borelAlgebraReal_eq_borel
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
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

theorem solution (a : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ioi a) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ioi
