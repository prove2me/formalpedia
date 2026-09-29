-- Prove2me | solution 1 for mme_CW_q6_primary_star_cyclic_hash_fiber_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:53:50.457577+00:00
-- url     : https://prove2.me/submissions/06624334-78f3-4cf0-864f-5c223b337127

import Definitions.Def_coupledQ6OrientedSurvivor
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_permutation
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_CW_coupled_cyclic_low_MM_restrict

open MME BigOperators

universe u

namespace CyclicHashFiberAssemblyScratch

theorem cyclic_eq_public
    {K : Type u} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X =
      TensorObj.kron X
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm X)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

theorem oriented_cyclic_iso
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (coupledQ6OrientedSurvivor K L G))
      (coupledQ6Survivor K L G) := by
  apply TensorQ.toQ_eq_iff.mp
  unfold coupledQ6OrientedSurvivor coupledQ6Survivor
  simp_rw [cyclic_eq_public]
  simp_rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow]
  simp_rw [← TensorQ.permAut_toQ]
  simp_rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow, map_mul, map_pow]
  simp_rw [← TensorQ.permAut_toQ]
  ring

theorem solution
    {K : Type u} [Field K] (L G A H : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
        TensorObj.kron (MMObj K H H H)
          (coupledQ6Survivor K L G)))
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A =>
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G)))) := by
  let C : TensorObj K 3 := MMObj K 1 H 1
  let S : TensorObj K 3 := coupledQ6OrientedSurvivor K L G
  let Q := TensorQ.tensorStrassen K 3 (by norm_num)
  have hC : Q.le
      (TensorQ.toQ (MMObj K H H H))
      (TensorQ.toQ (cyclicSymmetrization C)) := by
    exact mme_CW_coupled_cyclic_low_MM_restrict (K := K) H
  have hS : Q.le
      (TensorQ.toQ (coupledQ6Survivor K L G))
      (TensorQ.toQ (cyclicSymmetrization S)) := by
    exact (oriented_cyclic_iso (K := K) L G).2
  have hfirst := Q.mul_right _ _ hC
    (TensorQ.toQ (coupledQ6Survivor K L G))
  have hsecond := Q.mul_right _ _ hS
    (TensorQ.toQ (cyclicSymmetrization C))
  have hproduct : Q.le
      (TensorQ.toQ (MMObj K H H H) *
        TensorQ.toQ (coupledQ6Survivor K L G))
      (TensorQ.toQ (cyclicSymmetrization C) *
        TensorQ.toQ (cyclicSymmetrization S)) := by
    apply Q.le_trans _
      (TensorQ.toQ (cyclicSymmetrization C) *
        TensorQ.toQ (coupledQ6Survivor K L G)) _
    · exact hfirst
    · simpa only [mul_comm] using hsecond
  have hscaled := Q.mul_right _ _ hproduct
    ((A ^ 3 : ℕ) : TensorQ K 3)
  have htarget :
      TensorQ.toQ
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L G))) =
        ((A ^ 3 : ℕ) : TensorQ K 3) *
          (TensorQ.toQ (MMObj K H H H) *
            TensorQ.toQ (coupledQ6Survivor K L G)) := by
    rw [TensorQ.toQ_bigAdd]
    simp only [TensorQ.toQ_kron, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul]
  have hsource :
      TensorQ.toQ
          (cyclicSymmetrization
            (TensorObj.bigAdd (fun _ : Fin A =>
              TensorObj.kron C S))) =
        ((A ^ 3 : ℕ) : TensorQ K 3) *
          (TensorQ.toQ (cyclicSymmetrization C) *
            TensorQ.toQ (cyclicSymmetrization S)) := by
    simp_rw [cyclic_eq_public]
    simp_rw [TensorQ.toQ_kron, TensorQ.toQ_bigAdd]
    simp_rw [← TensorQ.permAut_toQ]
    simp_rw [TensorQ.toQ_kron, TensorQ.toQ_bigAdd]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      map_mul, map_natCast]
    simp_rw [TensorQ.toQ_kron]
    simp only [map_mul, Nat.cast_pow]
    ring
  change Q.le
    (TensorQ.toQ
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
        TensorObj.kron (MMObj K H H H)
          (coupledQ6Survivor K L G))))
    (TensorQ.toQ
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A =>
          TensorObj.kron C S))))
  rw [htarget, hsource]
  simpa only [mul_comm] using hscaled

end CyclicHashFiberAssemblyScratch

/-- Public proof wrapper for cyclic assembly of one constant primary-star
family. -/
theorem solution
    {K : Type u} [Field K] (L G A H : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin (A ^ 3) ↦
        TensorObj.kron (MMObj K H H H)
          (coupledQ6Survivor K L G)))
      (cyclicSymmetrization
        (TensorObj.bigAdd (fun _ : Fin A ↦
          TensorObj.kron (MMObj K 1 H 1)
            (coupledQ6OrientedSurvivor K L G)))) :=
  CyclicHashFiberAssemblyScratch.solution L G A H
