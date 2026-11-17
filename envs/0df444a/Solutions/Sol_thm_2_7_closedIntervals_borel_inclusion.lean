-- Prove2me | solution 1 for thm_2_7_closedIntervals_borel_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:52:09.771651+00:00
-- url     : https://prove2.me/submissions/6627f286-3565-4b69-b717-bac0469cf436

import Theorems.Thm_closedInterval_mem_borelAlgebraReal
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

theorem solution :
    MeasurableSpace.generateFrom realStrictClosedIntervals ≤ borelAlgebraReal := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨a, b, _hab, rfl⟩
  exact closedInterval_mem_borelAlgebraReal a b
