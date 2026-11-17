-- Prove2me | solution 1 for euclideanOpenBall_eq_countable_biUnion_openBoxes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:10:10.132693+00:00
-- url     : https://prove2.me/submissions/2e1d4837-d156-428e-92d0-f3c2e1708d79

import Theorems.Thm_euclideanOpenBoxes_isTopologicalBasis
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
    (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (_hr : 0 < r) :
    ∃ S ⊆ euclideanOpenBoxes d, S.Countable ∧
      Metric.ball c r = ⋃ s ∈ S, s := by
  exact (euclideanOpenBoxes_isTopologicalBasis d).exists_countable_biUnion_of_isOpen
    Metric.isOpen_ball
