-- Prove2me | solution 1 for mme_dwz_labelled_sum_useful_block_tensors_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:18:58.324984+00:00
-- url     : https://prove2.me/submissions/37c7fe5d-ea12-4ddd-b4b3-cbdd2d0f917b

import Theorems.Thm_mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) :
    (∑ block : DWZStandardBlock m,
        dwzLabelledUsefulBlockTensor K m D block) = D.X.t := by
  classical
  let allCopy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m) :=
    { nonholes := Finset.univ }
  let G := D.X.basisZAllowedGrading D.basis
    (fun W ↦ D.label W ∈ allCopy.nonholes)
  have hinclusion :
      PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
          (G.blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          dwzLabelledUsefulBlockTensor K m D block := by
    have h := mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
      K m D allCopy
    change PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t = _ at h
    simpa only [allCopy] using h
  have hprojection :
      D.basis.constr K
          (fun W ↦ if D.label W ∈ allCopy.nonholes then
            D.basis W else 0) =
        LinearMap.id := by
    apply D.basis.ext
    intro W
    rw [Module.Basis.constr_basis]
    simp only [allCopy, Finset.mem_univ, if_true, LinearMap.id_apply]
  have hcomplete :
      PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
          (G.blockSubtensor (fun _ ↦ 0)).t = D.X.t := by
    rw [mme_basisZAllowed_blockSubtensor_inclusion_tensor]
    rw [hprojection, Function.update_eq_self,
      PiTensorProduct.map_id, LinearMap.id_apply]
  exact hinclusion.symm.trans hcomplete
