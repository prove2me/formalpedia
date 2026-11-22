-- Prove2me | solution 1 for interpClassFixed_eq_range_patchEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:49.424617+00:00
-- url     : https://prove2.me/submissions/dcff6acf-c1fc-48ba-b1ea-d6ff50820ecb

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
theorem _root_.solution
    {X : Type u}
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSet A)) := by
  ext h
  simp only [interpClassFixed, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨θ₁, rfl⟩, _, ⟨θ₂, rfl⟩, rfl⟩
    refine ⟨(θ₁, θ₂, ()), funext fun x => ?_⟩
    simp only [patchEval, routerOfSet, piecewiseConcept]
    split <;> simp_all
  · rintro ⟨⟨θ₁, θ₂, _⟩, rfl⟩
    refine ⟨e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, funext fun x => ?_⟩
    simp only [patchEval, routerOfSet, piecewiseConcept]
    split <;> simp_all
