-- Prove2me | solution 1 for euclideanOpenBox_mem_generateFrom_openBalls
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:12:14.140197+00:00
-- url     : https://prove2.me/submissions/061de62a-17c3-45ec-a14d-245ce2aef58b

import Theorems.Thm_euclideanOpenBox_eq_countable_biUnion_openBalls
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
    (d : ℕ) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S ∈ euclideanOpenBoxes d) :
    @MeasurableSet (EuclideanSpace ℝ (Fin d))
      (MeasurableSpace.generateFrom (euclideanOpenBalls d)) S := by
  rcases euclideanOpenBox_eq_countable_biUnion_openBalls d hS with
    ⟨T, hTsub, hTcount, hEq⟩
  rw [hEq]
  exact MeasurableSet.biUnion hTcount fun t ht =>
    measurableSet_generateFrom (hTsub ht)
