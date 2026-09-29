-- Prove2me | solution 1 for mme_dwz_source_broken_family_transport_to_grouped_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:56:57.357991+00:00
-- url     : https://prove2.me/submissions/59e0b885-10f4-401e-98f9-651c9220dedf

import Theorems.Thm_mme_dwz_source_broken_owner_restrict_grouped_standard
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (houter : ∀ j : Fin k, ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer j r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hSource : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        DWZSourceAligned.brokenAddressObj K m (outer j) (copy j))) S) :
    ∃ standardCopy : Fin k → DWZSquare.BrokenBlockCopy
        (DWZComponentRestriction.DWZStandardBlock m),
      (∀ j : Fin k,
        (standardCopy j).nonholes.card = (copy j).nonholes.card) ∧
      let D : DWZComponentRestriction.DWZStandardLabelledData K m :=
        { X := TensorObj.kronFin 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m)
          basis := TensorObj.kronFinModePiBasis 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m) 2
            (fun r ↦
              DWZComponentRestriction.restrictedComponentZBasis K r m)
          label := DWZComponentRestriction.groupedUsefulBlock m }
      let G : Fin k → D.X.TypeGrading 2 := fun j ↦
        D.X.basisZAllowedGrading D.basis
          (fun W ↦ D.label W ∈ (standardCopy j).nonholes)
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦
          (G j).blockSubtensor (fun _ ↦ 0))) S := by
  classical
  have hOwner : ∀ j : Fin k,
      ∃ transported : DWZSquare.BrokenBlockCopy
          (DWZComponentRestriction.DWZStandardBlock m),
        transported.nonholes.card = (copy j).nonholes.card ∧
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
          (DWZSourceAligned.brokenAddressObj K m
            (outer j) (copy j)) := by
    intro j
    exact mme_dwz_source_broken_owner_restrict_grouped_standard
      (outer j) (houter j) hm (copy j)
  let standardCopy : Fin k → DWZSquare.BrokenBlockCopy
      (DWZComponentRestriction.DWZStandardBlock m) :=
    fun j ↦ Classical.choose (hOwner j)
  have hCard : ∀ j : Fin k,
      (standardCopy j).nonholes.card = (copy j).nonholes.card := by
    intro j
    exact (Classical.choose_spec (hOwner j)).1
  have hGrouped : ∀ j : Fin k, TensorObj.Restrict
      ((TensorObj.kronFin 15 (fun s ↦
          DWZComponentRestriction.restrictedComponentPower K s m)).basisZAllowedSubtensor
        (TensorObj.kronFinModePiBasis 15
          (fun s ↦
            DWZComponentRestriction.restrictedComponentPower K s m) 2
          (fun s ↦
            DWZComponentRestriction.restrictedComponentZBasis K s m))
        (fun Wg ↦ DWZComponentRestriction.groupedUsefulBlock m Wg ∈
          (standardCopy j).nonholes))
      (DWZSourceAligned.brokenAddressObj K m
        (outer j) (copy j)) := by
    intro j
    exact (Classical.choose_spec (hOwner j)).2
  refine ⟨standardCopy, hCard, ?_⟩
  exact TensorObj.Restrict.trans
    (mme_bigAdd_mono_restrict hGrouped) hSource
