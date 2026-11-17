-- Prove2me | solution 1 for thm_2_7_mathlib_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:27:45.187325+00:00
-- url     : https://prove2.me/submissions/caca70bb-8014-4ecc-8d8f-5eb0a30fc3e3

import Theorems.Thm_borelAlgebraReal_eq_borel
import Theorems.Thm_thm_2_7
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
    MeasurableSpace.generateFrom realStrictClosedIntervals = borel ℝ := by
  rw [thm_2_7, borelAlgebraReal_eq_borel]
