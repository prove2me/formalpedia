-- Prove2me | solution 1 for mme_restrict_kronPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:52:55.323715+00:00
-- url     : https://prove2.me/submissions/5f851b2f-9692-4b98-9245-4099ae1f45b2

import Definitions.Def_mme_tensor_quotient

open MME

universe u


theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) (N : ℕ) :
    TensorObj.Restrict (X.kronPow N) (Y.kronPow N) := by
  induction N with
  | zero => exact TensorObj.Restrict.refl _
  | succ N ih =>
      change TensorObj.Restrict
        (TensorObj.kron X (X.kronPow N))
        (TensorObj.kron Y (Y.kronPow N))
      let P := TensorQ.tensorStrassen K 3 (by norm_num)
      have hx : P.le (TensorQ.toQ X) (TensorQ.toQ Y) := h
      have hp : P.le (TensorQ.toQ (X.kronPow N))
          (TensorQ.toQ (Y.kronPow N)) := ih
      have hleft := P.mul_right _ _ hx (TensorQ.toQ (X.kronPow N))
      have hright := P.mul_right _ _ hp (TensorQ.toQ Y)
      have hmul : P.le
          (TensorQ.toQ X * TensorQ.toQ (X.kronPow N))
          (TensorQ.toQ Y * TensorQ.toQ (Y.kronPow N)) := by
        exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)
      exact hmul
