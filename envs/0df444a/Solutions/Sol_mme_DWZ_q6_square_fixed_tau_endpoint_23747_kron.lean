-- Prove2me | solution 1 for mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:58:17.702619+00:00
-- url     : https://prove2.me/submissions/d4d50db8-653a-4ccb-a09c-b48e66127d54

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_strassen_lt_three_mul_of_tau_value_surplus

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (hV : HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23747 / 30000) (640001 / 10000)) :
    matMulExp_strassen K < 23747 / 10000 := by
  have hR :
      tensorAsymptoticRank
        (TensorObj.kron (CWObj K 6) (CWObj K 6)) ≤ (64 : ℝ) := by
    have h := mme_CW_square_asymptoticRank_le (K := K) 6
    norm_num at h ⊢
    exact h
  have h := mme_strassen_lt_three_mul_of_tau_value_surplus
    (K := K) (T := TensorObj.kron (CWObj K 6) (CWObj K 6))
    (tau := (23747 / 30000 : ℝ)) (V := (640001 / 10000 : ℝ))
    (R := (64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hR hV (by norm_num)
  norm_num at h ⊢
  exact h
