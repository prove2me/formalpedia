-- Prove2me | solution 1 for interpClass_wellBehaved_of_routerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:56.403484+00:00
-- url     : https://prove2.me/submissions/c197f65c-e598-42b2-bf0f-470170711d5d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
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
    (R : BorelRouterCode X) :
    WellBehavedVCMeasTarget X
      (Set.range (letI := R.instMeasΡ; patchEval e₁ e₂ R.eval)) := by
  let := R.instMeasΡ
  let := R.instStdΡ
  exact patch_borel_param_wellBehavedVCMeasTarget e₁ e₂ R.eval he₁ he₂ R.eval_meas
