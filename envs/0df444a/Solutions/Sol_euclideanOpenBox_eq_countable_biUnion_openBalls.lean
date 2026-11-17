-- Prove2me | solution 1 for euclideanOpenBox_eq_countable_biUnion_openBalls
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:10:18.278105+00:00
-- url     : https://prove2.me/submissions/698f20a6-457e-47a8-93c5-9f19621f43f3

import Theorems.Thm_metricOpenBalls_isTopologicalBasis
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
    (d : ℕ) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S ∈ euclideanOpenBoxes d) :
    ∃ T ⊆ euclideanOpenBalls d, T.Countable ∧ S = ⋃ t ∈ T, t := by
  have hballBasis :
      TopologicalSpace.IsTopologicalBasis
        {T : Set (EuclideanSpace ℝ (Fin d)) |
          ∃ c : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ T = Metric.ball c r} :=
    metricOpenBalls_isTopologicalBasis (α := EuclideanSpace ℝ (Fin d))
  have hSopen : IsOpen S := (euclideanOpenBoxes_isTopologicalBasis d).isOpen hS
  simpa [euclideanOpenBalls] using hballBasis.exists_countable_biUnion_of_isOpen hSopen
