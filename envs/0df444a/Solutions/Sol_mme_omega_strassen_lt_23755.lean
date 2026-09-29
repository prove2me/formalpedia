-- Prove2me | solution 1 for mme_omega_strassen_lt_23755
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:17:58.495262+00:00
-- url     : https://prove2.me/submissions/e4d4113d-6b16-4018-a7d4-97611c7feea3

import Theorems.Thm_mme_CW_auxiliary_inequality_2376_profile
import Theorems.Thm_mme_CW_auxiliary_numeric_23755
import Theorems.Thm_mme_CW_endpoint_of_numeric_certificate

/-! Submission-ready structural assembly for the Strassen-form endpoint. -/

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 4751 / 2000 := by
  by_cases hsmall : matMulExp_strassen K < 2
  · exact lt_trans hsmall (by norm_num)
  · have homega : 2 ≤ matMulExp_strassen K := le_of_not_gt hsmall
    apply mme_CW_endpoint_of_numeric_certificate
        (4751 / 2000) (matMulExp_strassen K)
    · norm_num
      exact mme_CW_auxiliary_numeric_23755
    · exact mme_CW_auxiliary_inequality_2376_profile homega
