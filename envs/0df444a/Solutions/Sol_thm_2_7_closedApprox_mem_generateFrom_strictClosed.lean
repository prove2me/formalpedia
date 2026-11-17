-- Prove2me | solution 1 for thm_2_7_closedApprox_mem_generateFrom_strictClosed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:40:12.711925+00:00
-- url     : https://prove2.me/submissions/ada9ce13-7d10-4e04-bab2-f00850a0d38b

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
    (a b : ℝ) (n : ℕ) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (thm_2_7_closedApprox a b n) := by
  dsimp [thm_2_7_closedApprox]
  split_ifs with h
  · exact MeasurableSpace.measurableSet_generateFrom
      (show Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) ∈
          realStrictClosedIntervals from
        ⟨a + 1 / ((n : ℝ) + 1), b - 1 / ((n : ℝ) + 1), h, rfl⟩)
  · exact @MeasurableSet.empty ℝ
      (MeasurableSpace.generateFrom realStrictClosedIntervals)
