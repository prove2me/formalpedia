-- Prove2me | solution 1 for interpClassFixed_subset_amalgClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:40.273342+00:00
-- url     : https://prove2.me/submissions/f7167186-365d-4c53-8bfa-05ab725695d8

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Amalgamation

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u}
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (A : Set X) :
    interpClassFixed (Set.range e₁) (Set.range e₂) A ⊆
      amalgClass (fun _ : Θ₁ => ()) (fun _ : Θ₂ => ())
        (fun p => piecewiseConcept A (e₁ p.1) (e₂ p.2)) := by
  intro h hh
  simp only [interpClassFixed, Set.mem_ofPred_eq] at hh
  obtain ⟨h₁, ⟨θ₁, rfl⟩, h₂, ⟨θ₂, rfl⟩, rfl⟩ := hh
  simp only [amalgClass, relParamClass, agreementRel, Set.mem_ofPred_eq]
  exact ⟨(θ₁, θ₂), trivial, rfl⟩
