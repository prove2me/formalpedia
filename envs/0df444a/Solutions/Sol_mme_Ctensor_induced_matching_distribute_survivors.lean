-- Prove2me | solution 1 for mme_Ctensor_induced_matching_distribute_survivors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:22:50.377646+00:00
-- url     : https://prove2.me/submissions/e44b2690-864f-4073-b026-8fb6fcd5f48c

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_bridge

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (L G A H k : ℕ)
    (hmacro :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
          TensorObj.kron (MMObj K H H H)
            (coupledQ6Survivor K L G)))
        T)
    (hmatching :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1))
        (MMObj K H H H)) :
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.diagObj K 3 ((A ^ 3) * k))
        (coupledQ6Survivor K L G))
      T := by
  let S := coupledQ6Survivor K L G
  let QH := TensorQ.toQ (MMObj K H H H)
  let QS := TensorQ.toQ S
  let P := TensorQ.tensorStrassen K 3 (by norm_num)
  have hmatchQ : P.le (k : TensorQ K 3) QH := by
    change P.le
      (TensorQ.toQ
        (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1)))
      QH at hmatching
    rw [TensorQ.toQ_bigAdd] at hmatching
    have hone : TensorQ.toQ (MMObj K 1 1 1) =
        (1 : TensorQ K 3) := MMq_one
    simpa only [hone, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, mul_one] using hmatching
  have hmacroQ :
      P.le (((A ^ 3 : ℕ) : TensorQ K 3) * (QH * QS))
        (TensorQ.toQ T) := by
    change P.le
      (TensorQ.toQ
        (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
          TensorObj.kron (MMObj K H H H) S)))
      (TensorQ.toQ T) at hmacro
    rw [TensorQ.toQ_bigAdd] at hmacro
    simpa only [TensorQ.toQ_kron, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul] using hmacro
  have hinside : P.le ((k : TensorQ K 3) * QS) (QH * QS) :=
    P.mul_right _ _ hmatchQ QS
  have hscaled :
      P.le (((A ^ 3 : ℕ) : TensorQ K 3) * ((k : TensorQ K 3) * QS))
        (((A ^ 3 : ℕ) : TensorQ K 3) * (QH * QS)) := by
    simpa only [mul_comm] using
      P.mul_right _ _ hinside (((A ^ 3 : ℕ) : TensorQ K 3))
  have hfinal :
      P.le (((((A ^ 3) * k : ℕ) : TensorQ K 3)) * QS)
        (TensorQ.toQ T) := by
    apply P.le_trans _ _ _ ?_ hmacroQ
    simpa only [Nat.cast_mul, mul_assoc] using hscaled
  change P.le
    (TensorQ.toQ
      (TensorObj.kron
        (TensorObj.diagObj K 3 ((A ^ 3) * k)) S))
    (TensorQ.toQ T)
  rw [TensorQ.toQ_kron]
  exact hfinal
