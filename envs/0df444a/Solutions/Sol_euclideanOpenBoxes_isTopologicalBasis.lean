-- Prove2me | solution 1 for euclideanOpenBoxes_isTopologicalBasis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:07:26.104093+00:00
-- url     : https://prove2.me/submissions/f314bcee-a3c0-4b0b-b50a-7c3e5b387f27

import Theorems.Thm_openBoxes_isTopologicalBasis
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

theorem solution (d : ℕ) :
    TopologicalSpace.IsTopologicalBasis (euclideanOpenBoxes d) := by
  change TopologicalSpace.IsTopologicalBasis
    (Set.preimage (EuclideanSpace.equiv (Fin d) ℝ) '' openBoxes d)
  exact (openBoxes_isTopologicalBasis d).isInducing
    (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.isInducing
