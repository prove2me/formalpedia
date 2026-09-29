-- Prove2me | solution 1 for mme_MMObj_cyclicSymmetrization_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:08:21.420002+00:00
-- url     : https://prove2.me/submissions/7b3cb27b-e581-49de-b9f9-e441db17207b

import Mathlib.Tactic
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (cyclicSymmetrization (MMObj K n m p))
      (MMObj K (n * m * p) (n * m * p) (n * m * p)) := by
  rw [cyclicSymmetrization_eq_public_perm]
  have hinnerPerm := TensorQ.mul_respects_iso
    (MMObj_permObj_cyclic (K := K) n m p)
    (mme_MMObj_permObj_cyclic_sq (K := K) n m p)
  have hinnerMM := MMObj_kron_iso (K := K)
    p n m m p n
  have hinner : TensorObj.Isomorphic
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm (MMObj K n m p))
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (MMObj K n m p)))
      (MMObj K (p * m) (n * p) (m * n)) :=
    TensorObj.Isomorphic.trans hinnerPerm hinnerMM
  have houter := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (MMObj K n m p)) hinner
  have hMM := MMObj_kron_iso (K := K)
    n m p (p * m) (n * p) (m * n)
  have h := TensorObj.Isomorphic.trans houter hMM
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
