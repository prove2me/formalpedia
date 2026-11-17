-- Prove2me | solution 1 for rightClosedInfinite_mem_borelAlgebraReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:51:24.711127+00:00
-- url     : https://prove2.me/submissions/ffaba147-4169-43be-896a-9f0699d93d5a

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
    @MeasurableSet ℝ borelAlgebraReal (Set.Ici a) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ici
