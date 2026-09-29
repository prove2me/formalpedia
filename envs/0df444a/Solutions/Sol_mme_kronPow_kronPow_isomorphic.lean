-- Prove2me | solution 1 for mme_kronPow_kronPow_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:10:31.619745+00:00
-- url     : https://prove2.me/submissions/ec4df070-2c81-4b4d-bf99-cf5d8cc258ed

import Definitions.Def_mme_rank_bridge

open MME

universe u

theorem solution
    {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) (m r : ℕ) :
    TensorObj.Isomorphic
      ((X.kronPow m).kronPow r)
      (X.kronPow (r * m)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow,
    TensorQ.toQ_kronPow]
  simpa [Nat.mul_comm] using (pow_mul (TensorQ.toQ X) m r).symm
