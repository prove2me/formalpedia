-- Prove2me | solution 1 for mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:55:46.655816+00:00
-- url     : https://prove2.me/submissions/8eb6b18c-f4b7-4726-abd7-19a5a4b6df55

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_mode_pi_basis
import Theorems.Thm_mme_dwz_table2_grouped_kronFin_shuffle_automorphism
import Theorems.Thm_mme_dwz_labelled_broken_shuffle_expansion

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
      (groupedOuter (m := m))) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
          (fun s ↦ restrictedComponentZBasis K s m)
        label := groupedUsefulBlock m }
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    let move : Equiv.Perm (DWZStandardBlock m) := MulAction.toPerm g
    ∃ shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzLabelledUsefulBlockTensor K m D block
          else 0 := by
  classical
  dsimp only
  rcases mme_dwz_table2_grouped_kronFin_shuffle_automorphism
      (K := K) m g with ⟨F, hFtensor, hFbasis⟩
  exact mme_dwz_labelled_broken_shuffle_expansion
    K m
    { X := TensorObj.kronFin 15
        (fun s : Fin 15 ↦ restrictedComponentPower K s m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun s : Fin 15 ↦ restrictedComponentPower K s m) 2
        (fun s ↦ restrictedComponentZBasis K s m)
      label := groupedUsefulBlock m }
    copy (MulAction.toPerm g) F hFtensor hFbasis
