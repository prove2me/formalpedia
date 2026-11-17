-- Prove2me | solution 1 for euclideanOpenBall_mem_generateFrom_openBoxes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:12:03.286295+00:00
-- url     : https://prove2.me/submissions/3dc5b2f9-6191-4cd7-ba42-74f8451776a8

import Theorems.Thm_euclideanOpenBall_eq_countable_biUnion_openBoxes
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

theorem solution
    (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    @MeasurableSet (EuclideanSpace ℝ (Fin d))
      (MeasurableSpace.generateFrom (euclideanOpenBoxes d)) (Metric.ball c r) := by
  rcases euclideanOpenBall_eq_countable_biUnion_openBoxes d c hr with
    ⟨S, hSsub, hScount, hEq⟩
  rw [hEq]
  exact MeasurableSet.biUnion hScount fun s hs =>
    measurableSet_generateFrom (hSsub hs)
