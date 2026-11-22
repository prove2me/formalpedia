-- Prove2me | solution 1 for measurableSet_agreementRel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:05.012705+00:00
-- url     : https://prove2.me/submissions/c4241d15-ad39-4d16-8fa1-8f076c4675de

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
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂) :
    MeasurableSet (agreementRel π₁ π₂) := by
  unfold agreementRel
  let := upgradeStandardBorel S
  exact measurableSet_eq_fun (hπ₁.comp measurable_fst) (hπ₂.comp measurable_snd)
