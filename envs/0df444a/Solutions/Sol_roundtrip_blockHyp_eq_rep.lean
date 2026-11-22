-- Prove2me | solution 1 for roundtrip_blockHyp_eq_rep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:42.665802+00:00
-- url     : https://prove2.me/submissions/15c31991-656e-4a6e-894f-a8762346089c

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
public import Theorems.Thm_decodeWitnessXCoords_encode_eq
public import Theorems.Thm_decodeWitnessLabel_eq_on_encoded
public import Theorems.Thm_labeledSampleOfFinset_eq_of_eq_on_support

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution
    {X : Type u} [DecidableEq X]
    (learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool))
    (kernel : Finset (X × Bool)) (c : X → Bool) (K : ℕ)
    (W : Finset X) (h : X → Bool)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1)
    (hrep : learn (labeledSampleOfFinset c W) = h)
    (x : X) :
    let info : Finset (Fin K) := encodeWitnessInfo kernel c K W
    let blockXCoords : Finset X := decodeWitnessXCoords kernel info
    let blockLabel : X → Bool := decodeWitnessLabel kernel
    learn (labeledSampleOfFinset blockLabel blockXCoords) x = h x := by
  dsimp
  have hcoords : decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W) = W :=
    decodeWitnessXCoords_encode_eq kernel c W hK hWker
  have hlabel : ∀ x ∈ W, decodeWitnessLabel kernel x = c x :=
    decodeWitnessLabel_eq_on_encoded kernel c W hWker hlabels
  rw [hcoords]
  have hsamp : labeledSampleOfFinset (decodeWitnessLabel kernel) W = labeledSampleOfFinset c W :=
    labeledSampleOfFinset_eq_of_eq_on_support hlabel
  rw [hsamp, hrep]
