-- Prove2me | solution 1 for mme_kron_self_kronPow_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:45:06.752981+00:00
-- url     : https://prove2.me/submissions/7390a98d-8e19-434c-b910-e1bf7cfefb89

import Definitions.Def_mme_rank_bridge

open MME

universe u

theorem solution
    {K : Type u} [Field K] {d : ℕ} (X : TensorObj K d) (N : ℕ) :
    TensorObj.Isomorphic
      ((TensorObj.kron X X).kronPow N)
      (X.kronPow (2 * N)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow, ← TensorQ.toQ_mul]
  simpa [pow_two] using
    (pow_mul (TensorQ.toQ X) 2 N).symm
