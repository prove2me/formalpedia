-- Prove2me | solution 1 for patch_borel_param_wellBehavedVCMeasTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:03.946179+00:00
-- url     : https://prove2.me/submissions/49416cd6-f08f-4af0-b9aa-5dbba256d058

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Theorems.Thm_borel_param_wellBehavedVCMeasTarget
public import Theorems.Thm_patchEval_measurable

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ Ρ : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace Ρ] [StandardBorelSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range (patchEval e₁ e₂ r)) :=
  borel_param_wellBehavedVCMeasTarget (patchEval e₁ e₂ r)
    (patchEval_measurable e₁ e₂ r he₁ he₂ hr)
