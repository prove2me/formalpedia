-- Prove2me | solution 1 for mme_diagObj_kron_isomorphic_bigAdd_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:25:40.114776+00:00
-- url     : https://prove2.me/submissions/c99a841b-567d-45f0-8efc-be2fadf485b1

import Definitions.Def_mme_rank_bridge

open MME BigOperators

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    (S : TensorObj K d) (n : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.kron (TensorObj.diagObj K d n) S)
      (TensorObj.bigAdd (fun _ : Fin n => S)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kron, ← TensorQ.natCast_eq,
    TensorQ.toQ_bigAdd, Finset.sum_const, Finset.card_fin]
  simpa [mul_comm] using (nsmul_eq_mul' (TensorQ.toQ S) n).symm
