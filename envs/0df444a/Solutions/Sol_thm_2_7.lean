-- Prove2me | solution 1 for thm_2_7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:11:54.709207+00:00
-- url     : https://prove2.me/submissions/f180c4c1-f7e7-447f-aadf-2d321e1ae7d3

import Theorems.Thm_thm_2_7_closedIntervals_borel_inclusion
import Theorems.Thm_thm_2_7_borelAlgebraReal_le_generateFrom_strictClosed
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
    MeasurableSpace.generateFrom realStrictClosedIntervals = borelAlgebraReal :=
  le_antisymm thm_2_7_closedIntervals_borel_inclusion
    thm_2_7_borelAlgebraReal_le_generateFrom_strictClosed
