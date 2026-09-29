-- Prove2me | solution 1 for mme_CW_2376_induced_family_direct_sum_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:27:16.834357+00:00
-- url     : https://prove2.me/submissions/c5060191-b7c7-4e6d-a5ce-683da8a8ea04

import Theorems.Thm_mme_CW_2376_induced_family_bigAdd_core_extraction
import Theorems.Thm_mme_diagObj_kron_isomorphic_bigAdd_const

open MME

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    TensorObj.Restrict
      (TensorObj.kron (TensorObj.diagObj K 3 F.card)
        (cw2376ProfileCore K m))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
        (cw2376ProfileLength m)) := by
  have hIso := mme_diagObj_kron_isomorphic_bigAdd_const
    (cw2376ProfileCore K m) F.card
  exact TensorObj.Restrict.trans hIso.1
    (mme_CW_2376_induced_family_bigAdd_core_extraction cert m F hF)
