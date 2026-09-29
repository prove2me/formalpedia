-- Prove2me | solution 1 for mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:51:50.340203+00:00
-- url     : https://prove2.me/submissions/74657eec-cd50-4e94-8bdc-87bdd1efa374

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open BigOperators Finset
open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : MME.DWZComponentRestriction.DWZStandardLabelledData K m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZComponentRestriction.DWZStandardBlock m)) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
        (G.blockSubtensor (fun _ ↦ 0)).t =
      ∑ block ∈ copy.nonholes,
        MME.DWZComponentRestriction.dwzLabelledUsefulBlockTensor
          K m D block := by
  classical
  dsimp only
  rw [mme_basisZAllowed_blockSubtensor_inclusion_tensor]
  have hproj :
      MME.DWZComponentRestriction.basisLabelProjection
          D.basis D.label copy.nonholes =
        ∑ block ∈ copy.nonholes,
          MME.DWZComponentRestriction.basisLabelProjection
            D.basis D.label {block} := by
    apply D.basis.ext
    intro W
    simp only [MME.DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, LinearMap.sum_apply,
      Finset.mem_singleton]
    change (if D.label W ∈ copy.nonholes then D.basis W else 0) =
      ∑ block ∈ copy.nonholes,
        if D.label W = block then D.basis W else 0
    by_cases hW : D.label W ∈ copy.nonholes
    · rw [if_pos hW]
      rw [Finset.sum_eq_single (D.label W)]
      · rw [if_pos rfl]
      · intro block hblock hne
        rw [if_neg (Ne.symm hne)]
      · intro hnot
        exact (hnot hW).elim
    · rw [if_neg hW]
      symm
      apply Finset.sum_eq_zero
      intro block hblock
      rw [if_neg]
      intro heq
      exact hW (heq ▸ hblock)
  change
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (MME.DWZComponentRestriction.basisLabelProjection
            D.basis D.label copy.nonholes)) D.X.t = _
  rw [hproj]
  unfold MME.DWZComponentRestriction.dwzLabelledUsefulBlockTensor
  let p := fun block : MME.DWZComponentRestriction.DWZStandardBlock m ↦
    MME.DWZComponentRestriction.basisLabelProjection
      D.basis D.label {block}
  change
    PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (∑ block ∈ copy.nonholes, p block)) D.X.t =
      ∑ block ∈ copy.nonholes,
        PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2 (p block)) D.X.t
  induction copy.nonholes using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have hzero := PiTensorProduct.map_update_smul
        (fun _ ↦ LinearMap.id : ∀ i, D.X.V i →ₗ[K] D.X.V i)
        (2 : Fin 3) (0 : K) (LinearMap.id : D.X.V 2 →ₗ[K] D.X.V 2)
      have h := LinearMap.congr_fun hzero D.X.t
      simp only [zero_smul] at h
      exact h
  | @insert block blocks hnot ih =>
      simp only [Finset.sum_insert hnot]
      rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
      rw [ih]
