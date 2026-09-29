-- Prove2me | solution 1 for mme_CW_2376_exact_address_block_restrict_profile_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:42:44.9958+00:00
-- url     : https://prove2.me/submissions/525d4a7f-12be-4293-aa05-cb827abd9ca4

import Theorems.Thm_mme_CW_2376_exact_address_block_quotient_count
import Theorems.Thm_mme_CW_2376_grouped_square_blocks_dominate_profile_core

open MME BigOperators

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (a : CW2376ExactProfileAddress m) :
    TensorObj.Restrict (cw2376ProfileCore K m)
      (cw2376ExactAddressBlock cert a) := by
  rw [← TensorQ.le_toQ]
  rw [mme_CW_2376_exact_address_block_quotient_count cert m a]
  exact mme_CW_2376_grouped_square_blocks_dominate_profile_core cert m
