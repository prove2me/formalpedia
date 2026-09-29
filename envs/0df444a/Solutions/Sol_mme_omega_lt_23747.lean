-- Prove2me | solution 1 for mme_omega_lt_23747
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:18:56.628987+00:00
-- url     : https://prove2.me/submissions/4014223d-c519-4336-9576-c7aaf902fcd7

import Theorems.Thm_mme_dwz_square_fixed_tau_value_23747
import Theorems.Thm_mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
import Theorems.Thm_mme_omega_eq_strassen

universe u

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution {K : Type u} [Field K] :
    matMulExp K < 23747 / 10000 := by
  rw [mme_omega_eq_strassen]
  exact mme_DWZ_q6_square_fixed_tau_endpoint_23747_kron
    (mme_dwz_square_fixed_tau_value_23747 (K := K))
