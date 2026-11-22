-- Prove2me | solution 1 for interpClassCountable_wellBehaved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:55.774035+00:00
-- url     : https://prove2.me/submissions/1837b8a0-bc26-45be-ac3f-9fe57e37c2e7

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Theorems.Thm_routerOfSetFamily_measurable
public import Theorems.Thm_interpClassCountable_eq_range_patchEval
public import Theorems.Thm_patch_borel_param_wellBehavedVCMeasTarget


set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n)) :
    WellBehavedVCMeasTarget X (interpClassCountable (Set.range e₁) (Set.range e₂) A) := by
  rw [interpClassCountable_eq_range_patchEval]
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ _ he₁ he₂
    (routerOfSetFamily_measurable hA)
