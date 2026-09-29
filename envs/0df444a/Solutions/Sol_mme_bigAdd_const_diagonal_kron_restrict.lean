-- Prove2me | solution 1 for mme_bigAdd_const_diagonal_kron_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:44:06.414665+00:00
-- url     : https://prove2.me/submissions/0b81bbff-467d-453f-88d5-754374001368

import Definitions.Def_mme_rank_bridge

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Pair equal labels in two constant direct sums and discard all off-diagonal
pairs. -/
theorem solution
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    (X Y : TensorObj K d) (k : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k ↦ TensorObj.kron X Y))
      (TensorObj.kron
        (TensorObj.bigAdd (fun _ : Fin k ↦ X))
        (TensorObj.bigAdd (fun _ : Fin k ↦ Y))) := by
  let P := TensorQ.tensorStrassen K d hd
  have hkNat : k ≤ k * k := by
    cases k with
    | zero => simp
    | succ k => nlinarith
  have hk : P.le
      ((k : ℕ) : TensorQ K d)
      (((k * k : ℕ) : TensorQ K d)) :=
    (P.nat_order_embedding k (k * k)).2 hkNat
  have hscaled := P.mul_right _ _ hk
    (TensorQ.toQ X * TensorQ.toQ Y)
  change P.le
    (TensorQ.toQ
      (TensorObj.bigAdd (fun _ : Fin k ↦ TensorObj.kron X Y)))
    (TensorQ.toQ
      (TensorObj.kron
        (TensorObj.bigAdd (fun _ : Fin k ↦ X))
        (TensorObj.bigAdd (fun _ : Fin k ↦ Y))))
  rw [TensorQ.toQ_kron
    (TensorObj.bigAdd (fun _ : Fin k ↦ X))
    (TensorObj.bigAdd (fun _ : Fin k ↦ Y))]
  rw [TensorQ.toQ_bigAdd (fun _ : Fin k ↦ TensorObj.kron X Y)]
  rw [TensorQ.toQ_bigAdd (fun _ : Fin k ↦ X)]
  rw [TensorQ.toQ_bigAdd (fun _ : Fin k ↦ Y)]
  simp_rw [TensorQ.toQ_kron X Y]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    using hscaled
