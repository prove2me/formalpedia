-- Prove2me | solution 1 for range_patchEval_sub_interpClass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:39.815732+00:00
-- url     : https://prove2.me/submissions/17b8584e-8d9d-49bb-8eab-ee03e4874f8c

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
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ : Type*}
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (R : BorelRouterCode X) :
    Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval) ⊆
      interpClass (Set.range e₁) (Set.range e₂) := by
  rintro h ⟨⟨θ₁, θ₂, ρ⟩, rfl⟩
  simp only [interpClass, Set.mem_ofPred_eq]
  refine ⟨{x | R.eval ρ x = true}, ?_, e₁ θ₁, ⟨θ₁, rfl⟩, e₂ θ₂, ⟨θ₂, rfl⟩, ?_⟩
  · let := R.instMeasΡ
    have hm : Measurable (fun x => R.eval ρ x) :=
      R.eval_meas.comp (Measurable.prodMk measurable_const measurable_id)
    exact hm (measurableSet_singleton true)
  · funext x
    simp only [patchEval, piecewiseConcept, Set.mem_ofPred_eq]
    split <;> rfl
