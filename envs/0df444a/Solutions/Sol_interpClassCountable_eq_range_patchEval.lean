-- Prove2me | solution 1 for interpClassCountable_eq_range_patchEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:52.834519+00:00
-- url     : https://prove2.me/submissions/40bd5c8f-4b6d-4b1d-b198-f03be8a2a5fa

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
    (A : ℕ → Set X) :
    interpClassCountable (Set.range e₁) (Set.range e₂) A =
      Set.range (patchEval e₁ e₂ (routerOfSetFamily A)) := by
  ext h
  simp only [interpClassCountable, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨n, _, ⟨θ₁, rfl⟩, _, ⟨θ₂, rfl⟩, rfl⟩
    refine ⟨(θ₁, θ₂, n), funext fun x => ?_⟩
    simp only [patchEval, routerOfSetFamily, piecewiseConcept]
    split <;> simp_all
  · rintro ⟨⟨θ₁, θ₂, n⟩, rfl⟩
    refine ⟨n, e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, funext fun x => ?_⟩
    simp only [patchEval, routerOfSetFamily, piecewiseConcept]
    split <;> simp_all
