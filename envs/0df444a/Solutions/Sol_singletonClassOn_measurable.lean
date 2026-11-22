-- Prove2me | solution 1 for singletonClassOn_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:45.130317+00:00
-- url     : https://prove2.me/submissions/d6da493f-1b40-4f03-aa3c-bdc040ebda97

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
theorem _root_.solution
    (A : Set ℝ) :
    ∀ h ∈ singletonClassOn A, Measurable h := by
  intro h hh
  rcases hh with rfl | ⟨a, _, rfl⟩
  · exact measurable_const
  · show Measurable (singletonConcept a)
    unfold singletonConcept
    exact Measurable.piecewise (measurableSet_singleton a) measurable_const measurable_const
