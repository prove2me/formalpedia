-- Prove2me | solution 1 for mme_dwz_source_broken_restrict_of_grouped_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:22:58.658213+00:00
-- url     : https://prove2.me/submissions/1bae6aa2-5f72-43bc-b36f-0b256e83ba73

import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_basisZAllowedSubtensor_restrict_of_basis_map

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (U : TensorObj K 3) {κ : Type u}
    (bU : Basis κ K (U.V 2))
    (label : κ → DWZComponentRestriction.DWZStandardBlock m)
    (transported : DWZSquare.BrokenBlockCopy
      (DWZComponentRestriction.DWZStandardBlock m))
    (blockEquiv : DWZTable2StandardForm.UsefulBlock m outer ≃
      DWZComponentRestriction.DWZStandardBlock m)
    (hTransport : ∀ small,
      blockEquiv small ∈ transported.nonholes ↔
        small ∈ copy.nonholes)
    (f : ∀ i : Fin 3,
      (DWZSourceAligned.coarseAddressObj K outer).V i →ₗ[K] U.V i)
    (hmap : PiTensorProduct.map f
      (DWZSourceAligned.coarseAddressObj K outer).t = U.t)
    (hBasisUseful : ∀ (W : DWZSourceAligned.AddressZWord.{u} outer)
      (hW : DWZSourceAligned.addressWordUseful m outer W),
      ∃ Wg : κ,
        f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = bU Wg ∧
        label Wg = blockEquiv
          (DWZSourceAligned.addressUsefulBlock m outer W hW))
    (hBasisZero : ∀ W : DWZSourceAligned.AddressZWord.{u} outer,
      ¬ DWZSourceAligned.addressWordUseful m outer W →
        f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = 0) :
    TensorObj.Restrict
      (U.basisZAllowedSubtensor bU
        (fun Wg ↦ label Wg ∈ transported.nonholes))
      (DWZSourceAligned.brokenAddressObj K m outer copy) := by
  classical
  let routed : ∀ W : DWZSourceAligned.AddressZWord.{u} outer,
      DWZSourceAligned.addressWordUseful m outer W → κ :=
    fun W hW ↦ Classical.choose (hBasisUseful W hW)
  have routed_spec : ∀ (W : DWZSourceAligned.AddressZWord.{u} outer)
      (hW : DWZSourceAligned.addressWordUseful m outer W),
      f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) =
          bU (routed W hW) ∧
        label (routed W hW) = blockEquiv
          (DWZSourceAligned.addressUsefulBlock m outer W hW) := by
    intro W hW
    exact Classical.choose_spec (hBasisUseful W hW)
  let σ : DWZSourceAligned.AddressZWord.{u} outer → Option κ :=
    fun W ↦ if hW : DWZSourceAligned.addressWordUseful m outer W then
      some (routed W hW) else none
  have hNone : ∀ W, σ W = none →
      f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = 0 := by
    intro W hσ
    by_cases hW : DWZSourceAligned.addressWordUseful m outer W
    · simp [σ, hW] at hσ
    · exact hBasisZero W hW
  have hSome : ∀ W Wg, σ W = some Wg →
      f 2 (DWZSourceAligned.coarseAddressZBasis K outer W) = bU Wg := by
    intro W Wg hσ
    by_cases hW : DWZSourceAligned.addressWordUseful m outer W
    · have heq : routed W hW = Wg := by
        simpa only [σ, dif_pos hW, Option.some.injEq] using hσ
      simpa only [heq] using (routed_spec W hW).1
    · simp [σ, hW] at hσ
  have hAllowed : ∀ W Wg, σ W = some Wg →
      (DWZSourceAligned.addressWordSurvives m outer copy W ↔
        label Wg ∈ transported.nonholes) := by
    intro W Wg hσ
    have hW : DWZSourceAligned.addressWordUseful m outer W := by
      by_contra hn
      simp [σ, hn] at hσ
    have heq : routed W hW = Wg := by
      simpa only [σ, dif_pos hW, Option.some.injEq] using hσ
    have hlabel : label Wg = blockEquiv
        (DWZSourceAligned.addressUsefulBlock m outer W hW) := by
      simpa only [heq] using (routed_spec W hW).2
    constructor
    · rintro ⟨hW', hmem⟩
      have hsmall :
          DWZSourceAligned.addressUsefulBlock m outer W hW' =
            DWZSourceAligned.addressUsefulBlock m outer W hW := by
        apply Subtype.ext
        rfl
      have hmem' : DWZSourceAligned.addressUsefulBlock m outer W hW ∈
          copy.nonholes := by
        simpa only [hsmall] using hmem
      rw [hlabel]
      exact (hTransport _).2 hmem'
    · intro hmem
      refine ⟨hW, ?_⟩
      apply (hTransport _).1
      simpa only [hlabel] using hmem
  have h := mme_basisZAllowedSubtensor_restrict_of_basis_map
    (DWZSourceAligned.coarseAddressObj K outer) U
      (DWZSourceAligned.coarseAddressZBasis K outer) bU
      (DWZSourceAligned.addressWordSurvives m outer copy)
      (fun Wg ↦ label Wg ∈ transported.nonholes)
      f hmap σ hNone hSome hAllowed
  simpa only [DWZSourceAligned.brokenAddressObj,
    DWZSourceAligned.brokenAddressGrading,
    TensorObj.basisZAllowedSubtensor] using h
