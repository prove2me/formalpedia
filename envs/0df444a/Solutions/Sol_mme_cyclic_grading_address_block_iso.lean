-- Prove2me | solution 1 for mme_cyclic_grading_address_block_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:52:28.251425+00:00
-- url     : https://prove2.me/submissions/cad6943d-10d8-4a63-8f5a-a6126ce8c8c1

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_cyclic_triple_grading
import Theorems.Thm_mme_cyclic_triple_grading_block_subtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators TensorObj.TypeGrading

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t)
    (a b c : Fin 3 → Fin N → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (gradedAddressBlock G a)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (gradedAddressBlock G b))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (gradedAddressBlock G c))))
      (gradedAddressBlock (mmeCyclicTripleGrading G)
        (fun i j ↦ mmeCyclicTripleGrade
          (fun s ↦ a s j) (fun s ↦ b s j) (fun s ↦ c s j) i)) := by
  let X : Fin N → TensorObj K 3 := fun j ↦
    G.blockSubtensor (fun i ↦ a i j)
  let Y : Fin N → TensorObj K 3 := fun j ↦
    G.blockSubtensor (fun i ↦ b i j)
  let Z : Fin N → TensorObj K 3 := fun j ↦
    G.blockSubtensor (fun i ↦ c i j)
  let C : Fin N → TensorObj K 3 := fun j ↦
    (mmeCyclicTripleGrading G).blockSubtensor
      (mmeCyclicTripleGrade
        (fun s ↦ a s j) (fun s ↦ b s j) (fun s ↦ c s j))
  let P : Fin N → TensorObj K 3 := fun j ↦
    TensorObj.kron (X j)
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm (Y j))
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (Z j)))
  have hpoint : ∀ j, TensorObj.Isomorphic (P j) (C j) := by
    intro j
    have hcyc := mme_cyclic_triple_grading_block_subtensor_iso
      G (fun s ↦ a s j) (fun s ↦ b s j) (fun s ↦ c s j)
    have hy := TensorObj.TypeGrading.permObjGrading_blockSubtensor_iso
      G cyclicPerm (fun s ↦ b s j)
    have hz := TensorObj.TypeGrading.permObjGrading_blockSubtensor_iso
      G (cyclicPerm.trans cyclicPerm) (fun s ↦ c s j)
    have hinner := TensorQ.mul_respects_iso hy hz
    have hlift := TensorQ.mul_respects_iso
      (TensorObj.Isomorphic.refl (X j)) hinner
    exact hlift.symm.trans hcyc
  have hfamily : TensorObj.Isomorphic
      (TensorObj.kronFin N P) (TensorObj.kronFin N C) :=
    mme_kronFin_respects_iso N P C hpoint
  have hdistrib : TensorObj.Isomorphic
      (TensorObj.kron (TensorObj.kronFin N X)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (TensorObj.kronFin N Y))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.kronFin N Z))))
      (TensorObj.kronFin N P) := by
    apply TensorQ.toQ_eq_iff.mp
    rw [TensorQ.toQ_kron, TensorQ.toQ_kron,
      ← TensorQ.permAut_toQ, ← TensorQ.permAut_toQ,
      mme_toQ_kronFin, mme_toQ_kronFin, mme_toQ_kronFin,
      map_prod, map_prod, mme_toQ_kronFin]
    simp only [P, TensorQ.toQ_kron,
      TensorQ.permAut_toQ, X, Y, Z]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  change TensorObj.Isomorphic
      (TensorObj.kron (TensorObj.kronFin N X)
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm (TensorObj.kronFin N Y))
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.kronFin N Z))))
      (TensorObj.kronFin N C)
  exact hdistrib.trans hfamily
