-- Prove2me | solution 1 for routerOfSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:46.153803+00:00
-- url     : https://prove2.me/submissions/c04bb9b2-501b-49ba-bec7-b18b5b8f8ddd

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem _root_.solution {X : Type u} [MeasurableSpace X]
    {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun p : Unit × X => routerOfSet A p.1 p.2) := by
  simp only [routerOfSet]
  exact Measurable.piecewise (measurable_snd hA) measurable_const measurable_const
