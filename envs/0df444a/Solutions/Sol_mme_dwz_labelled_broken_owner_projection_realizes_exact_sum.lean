-- Prove2me | solution 1 for mme_dwz_labelled_broken_owner_projection_realizes_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:01:10.522902+00:00
-- url     : https://prove2.me/submissions/fa538cbb-d75b-4b68-9d95-c28cbfa50dd5

import Theorems.Thm_mme_dwz_owner_projection_standard_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m) {s : ℕ}
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (owner : DWZStandardBlock m → Fin s) (t : Fin s) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    ∀ (shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i),
      (PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
          ∑ block : DWZStandardBlock m,
            if move.symm block ∈ copy.nonholes then
              dwzLabelledUsefulBlockTensor K m D block
            else 0) →
      (∀ block : DWZStandardBlock m, t = owner block →
        move.symm block ∈ copy.nonholes) →
      ∃ f : ∀ i,
          (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
        f 0 = shuffleMap 0 ∧
        f 1 = shuffleMap 1 ∧
        PiTensorProduct.map f (G.blockSubtensor (fun _ ↦ 0)).t =
          ∑ block : DWZStandardBlock m,
            if t = owner block then
              dwzLabelledUsefulBlockTensor K m D block
            else 0 := by
  classical
  dsimp only
  intro shuffleMap hshuffle howner
  let ownerMaps : ∀ i, D.X.V i →ₗ[K] D.X.V i :=
    Function.update (fun _ ↦ LinearMap.id) 2
      (basisLabelProjection D.basis D.label
        (Finset.univ.filter (fun block ↦ t = owner block)))
  let G := D.X.basisZAllowedGrading D.basis
    (fun W ↦ D.label W ∈ copy.nonholes)
  let f : ∀ i,
      (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i := fun i ↦
    (ownerMaps i).comp (shuffleMap i)
  refine ⟨f, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · change PiTensorProduct.map
      (fun i ↦ ownerMaps i ∘ₗ shuffleMap i)
        (G.blockSubtensor (fun _ ↦ 0)).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    change PiTensorProduct.map
      (Function.update (fun _ ↦ LinearMap.id) 2
        (basisLabelProjection D.basis D.label
          (Finset.univ.filter (fun block ↦ t = owner block))))
      (PiTensorProduct.map shuffleMap
        (G.blockSubtensor (fun _ ↦ 0)).t) = _
    rw [hshuffle, map_sum]
    apply Finset.sum_congr rfl
    intro block _
    by_cases hs : move.symm block ∈ copy.nonholes
    · simp only [hs, if_true]
      exact mme_dwz_owner_projection_standard_useful_block_tensor
        K m D owner t block
    · have hnotOwned : t ≠ owner block := fun ho ↦
        hs (howner block ho)
      simp only [hs, if_false, map_zero, hnotOwned]
