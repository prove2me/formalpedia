-- Prove2me | solution 1 for mme_dwz_source_broken_owner_restrict_grouped_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:46:36.231774+00:00
-- url     : https://prove2.me/submissions/183a84d5-7855-454c-b7f2-2a637b5d4086

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
import Theorems.Thm_mme_dwz_source_broken_restrict_of_grouped_basis_router

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

namespace MME.DWZSourceAligned

private noncomputable def reindexUsefulBlockOwner
    (m : ℕ) {P Q : Type u} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (outerQ : Q → Fin 15) (outerP : P → Fin 15)
    (houter : ∀ p, outerQ (e p) = outerP p)
    (small : DWZTable2StandardForm.UsefulBlock m outerQ) :
    DWZTable2StandardForm.UsefulBlock m outerP := by
  refine ⟨fun p ↦ small.1 (e p), ?_, ?_⟩
  · intro p
    exact (small.2.1 (e p)).trans
      (congrArg DWZSquare.shapeZ (houter p))
  · intro s a
    let fiberEquiv :
        {p : P // outerP p = s ∧ (small.1 (e p)).1 = a} ≃
          {q : Q // outerQ q = s ∧ (small.1 q).1 = a} :=
      { toFun := fun p ↦
          ⟨e p.1, ⟨(houter p.1).trans p.2.1, p.2.2⟩⟩
        invFun := fun q ↦
          ⟨e.symm q.1, ⟨by
            rw [← houter (e.symm q.1)]
            simpa using q.2.1, by simpa using q.2.2⟩⟩
        left_inv := fun p ↦ by apply Subtype.ext; simp
        right_inv := fun q ↦ by apply Subtype.ext; simp }
    exact (Fintype.card_congr fiberEquiv).trans (small.2.2 s a)

private noncomputable def usefulBlockPositionEquivOwner
    (m : ℕ) {P Q : Type u} [Fintype P] [Fintype Q]
    (e : P ≃ Q) (outerQ : Q → Fin 15) (outerP : P → Fin 15)
    (houter : ∀ p, outerQ (e p) = outerP p) :
    DWZTable2StandardForm.UsefulBlock m outerQ ≃
      DWZTable2StandardForm.UsefulBlock m outerP := by
  let houterSymm : ∀ q, outerP (e.symm q) = outerQ q := by
    intro q
    simpa using (houter (e.symm q)).symm
  exact
    { toFun := reindexUsefulBlockOwner m e outerQ outerP houter
      invFun := reindexUsefulBlockOwner m e.symm outerP outerQ houterSymm
      left_inv := by
        intro small
        apply Subtype.ext
        funext q
        simp [reindexUsefulBlockOwner]
      right_inv := by
        intro small
        apply Subtype.ext
        funext p
        simp [reindexUsefulBlockOwner] }

private def reindexBrokenCopyOwner
    {Block Block' : Type u} [Fintype Block] [Fintype Block']
    [DecidableEq Block']
    (e : Block ≃ Block')
    (copy : DWZSquare.BrokenBlockCopy Block) :
    DWZSquare.BrokenBlockCopy Block' :=
  ⟨copy.nonholes.map e.toEmbedding⟩

/-- One exact source-order broken owner restricts to its canonically grouped
fifteen-component broken standard mask.  The transported copy preserves the
number of nonholes. -/
theorem sourceBrokenOwner_restrict_grouped_standard
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    ∃ transported : DWZSquare.BrokenBlockCopy
        (DWZComponentRestriction.DWZStandardBlock m),
      transported.nonholes.card = copy.nonholes.card ∧
      TensorObj.Restrict
        ((TensorObj.kronFin 15 (fun s ↦
            DWZComponentRestriction.restrictedComponentPower K s m)).basisZAllowedSubtensor
          (TensorObj.kronFinModePiBasis 15
            (fun s ↦
              DWZComponentRestriction.restrictedComponentPower K s m) 2
            (fun s ↦
              DWZComponentRestriction.restrictedComponentZBasis K s m))
          (fun Wg ↦ DWZComponentRestriction.groupedUsefulBlock m Wg ∈
            transported.nonholes))
        (brokenAddressObj K m outer copy) := by
  obtain ⟨e, he, f, hmap, hUseful, hZero⟩ :=
    mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
      (K := K) outer houter hm
  let U : TensorObj K 3 := TensorObj.kronFin 15 (fun s ↦
    DWZComponentRestriction.restrictedComponentPower K s m)
  let bU := TensorObj.kronFinModePiBasis 15
    (fun s ↦ DWZComponentRestriction.restrictedComponentPower K s m) 2
    (fun s ↦ DWZComponentRestriction.restrictedComponentZBasis K s m)
  let blockEquiv : DWZTable2StandardForm.UsefulBlock m outer ≃
      DWZComponentRestriction.DWZStandardBlock m :=
    usefulBlockPositionEquivOwner m e outer
      DWZComponentRestriction.groupedOuter he
  let transported : DWZSquare.BrokenBlockCopy
      (DWZComponentRestriction.DWZStandardBlock m) :=
    reindexBrokenCopyOwner blockEquiv copy
  refine ⟨transported, ?_, ?_⟩
  · change (copy.nonholes.map blockEquiv.toEmbedding).card =
      copy.nonholes.card
    exact Finset.card_map blockEquiv.toEmbedding
  · refine mme_dwz_source_broken_restrict_of_grouped_basis_router
      m outer copy U bU (DWZComponentRestriction.groupedUsefulBlock m)
      transported blockEquiv ?_ f ?_ ?_ hZero
    · intro small
      simp [transported, reindexBrokenCopyOwner]
    · simpa [U] using hmap
    · intro W hW
      obtain ⟨Wg, hBasis, hFine⟩ := hUseful W hW
      refine ⟨Wg, by simpa [bU] using hBasis, ?_⟩
      apply Subtype.ext
      funext p
      change DWZComponentRestriction.groupedFineZ Wg p =
        addressFineZ W (e p)
      exact hFine p

end MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer)) :
    ∃ transported : MME.DWZSquare.BrokenBlockCopy
        (MME.DWZComponentRestriction.DWZStandardBlock m),
      transported.nonholes.card = copy.nonholes.card ∧
      MME.TensorObj.Restrict
        ((MME.TensorObj.kronFin 15 (fun s ↦
            MME.DWZComponentRestriction.restrictedComponentPower K s m)).basisZAllowedSubtensor
          (MME.TensorObj.kronFinModePiBasis 15
            (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentPower K s m) 2
            (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentZBasis K s m))
          (fun Wg ↦ MME.DWZComponentRestriction.groupedUsefulBlock m Wg ∈
            transported.nonholes))
        (MME.DWZSourceAligned.brokenAddressObj K m outer copy) := by
  exact MME.DWZSourceAligned.sourceBrokenOwner_restrict_grouped_standard
    outer houter hm copy
