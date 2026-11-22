-- Prove2me | solution 1 for labeledSampleOfFinset_eq_of_eq_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:36.447072+00:00
-- url     : https://prove2.me/submissions/e3f56d4e-6f0e-4e89-90de-891b7dcfe341

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_FiniteVCApprox
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_FiniteSupportUC
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u}
    {ℓ₁ ℓ₂ : X → Bool} {Z : Finset X}
    (hℓ : ∀ x ∈ Z, ℓ₁ x = ℓ₂ x) :
    labeledSampleOfFinset ℓ₁ Z = labeledSampleOfFinset ℓ₂ Z := by
  funext j
  simp only [labeledSampleOfFinset]
  simp_all
