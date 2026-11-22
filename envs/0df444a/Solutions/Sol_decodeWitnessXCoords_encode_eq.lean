-- Prove2me | solution 1 for decodeWitnessXCoords_encode_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:33.048945+00:00
-- url     : https://prove2.me/submissions/9b8cd60f-9ebd-4c95-a03f-1f25ae16d86f

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
    (kernel : Finset (X × Bool)) (c : X → Bool) {K : ℕ}
    (W : Finset X)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel) :
    decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W) = W := by
  ext x
  constructor
  · intro hx
    unfold decodeWitnessXCoords at hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨idx, hidx_mem, hx⟩ := hx
    unfold encodeWitnessInfo at hidx_mem
    simp only [Finset.mem_biUnion] at hidx_mem
    obtain ⟨⟨x0, hx0W⟩, _, hidx_mem2⟩ := hidx_mem
    by_cases hmk : ((x0 : X), c x0) ∈ kernel
    · by_cases hlt : (kernel.equivFin ⟨(x0, c x0), hmk⟩).val < K
      · simp_all
      · simp [dif_pos hmk, dif_neg hlt] at hidx_mem2
    · simp [dif_neg hmk] at hidx_mem2
  · intro hxW
    have hmk : (x, c x) ∈ kernel := hWker x hxW
    have hltK : (kernel.equivFin ⟨(x, c x), hmk⟩).val < K :=
      lt_of_lt_of_le (kernel.equivFin ⟨(x, c x), hmk⟩).isLt hK
    -- Show idx is in the encoded set
    have hidx_in_enc : ⟨(kernel.equivFin ⟨(x, c x), hmk⟩).val, hltK⟩ ∈
        encodeWitnessInfo kernel c K W := by
      simp only [encodeWitnessInfo, Finset.mem_biUnion, Finset.mem_attach, true_and]
      exact ⟨⟨x, hxW⟩, by simp [hmk, hltK]⟩
    -- Show x is in the decoded set from that idx
    change x ∈ decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W)
    simp only [decodeWitnessXCoords, Finset.mem_biUnion]
    refine ⟨⟨(kernel.equivFin ⟨(x, c x), hmk⟩).val, hltK⟩, hidx_in_enc, ?_⟩
    simp_all
