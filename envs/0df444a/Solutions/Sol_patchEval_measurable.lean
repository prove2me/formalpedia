-- Prove2me | solution 1 for patchEval_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:42.917+00:00
-- url     : https://prove2.me/submissions/810118be-272a-4d63-8842-5e5bee091dc2

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    {Θ₁ Θ₂ Ρ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] [MeasurableSpace Ρ]
    (e₁ : Θ₁ → Concept X Bool) (e₂ : Θ₂ → Concept X Bool)
    (r : Ρ → Concept X Bool)
    (he₁ : Measurable (fun p : Θ₁ × X => e₁ p.1 p.2))
    (he₂ : Measurable (fun p : Θ₂ × X => e₂ p.1 p.2))
    (hr : Measurable (fun p : Ρ × X => r p.1 p.2)) :
    Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => patchEval e₁ e₂ r p.1 p.2) := by
  simp only [patchEval]
  have hpred : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => r p.1.2.2 p.2) :=
    hr.comp (Measurable.prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst)) measurable_snd)
  have hleft : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => e₁ p.1.1 p.2) :=
    he₁.comp (Measurable.prodMk
      (measurable_fst.comp measurable_fst) measurable_snd)
  have hright : Measurable (fun p : (Θ₁ × Θ₂ × Ρ) × X => e₂ p.1.2.1 p.2) :=
    he₂.comp (Measurable.prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst)) measurable_snd)
  have hset : MeasurableSet {p : (Θ₁ × Θ₂ × Ρ) × X | r p.1.2.2 p.2 = true} :=
    hpred (measurableSet_singleton true)
  exact Measurable.piecewise hset hleft hright
