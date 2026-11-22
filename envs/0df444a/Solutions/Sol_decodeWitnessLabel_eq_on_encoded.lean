-- Prove2me | solution 1 for decodeWitnessLabel_eq_on_encoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:36.050035+00:00
-- url     : https://prove2.me/submissions/78aae269-2cdb-436c-92e0-4ce40bb555e5

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
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) (W : Finset X)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1) :
    ∀ x ∈ W, decodeWitnessLabel kernel x = c x := by
  intro x hxW
  unfold decodeWitnessLabel
  by_cases hc : c x = true
  · have hmem : (x, true) ∈ kernel := by
      simpa [hc] using hWker x hxW
    simp [hmem, hc]
  · have hnot : (x, true) ∉ kernel := by
      intro htrue
      simp_all
    simp_all
