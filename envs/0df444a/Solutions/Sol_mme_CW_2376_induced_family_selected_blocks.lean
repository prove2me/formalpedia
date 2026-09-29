-- Prove2me | solution 1 for mme_CW_2376_induced_family_selected_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:33:54.783451+00:00
-- url     : https://prove2.me/submissions/ba00fbc2-eefa-4187-ac1c-2b4e6503a0dc

import Theorems.Thm_mme_CW_2376_induced_family_address_block_zeroing
import Theorems.Thm_mme_CW_2376_exact_address_block_restrict_profile_core

open MME

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    ∃ B : Fin F.card → TensorObj K 3,
      TensorObj.Restrict (TensorObj.bigAdd B)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
          (cw2376ProfileLength m)) ∧
      ∀ j, TensorObj.Restrict (cw2376ProfileCore K m) (B j) := by
  obtain ⟨e, hzero⟩ :=
    mme_CW_2376_induced_family_address_block_zeroing cert m F hF
  refine ⟨fun j => cw2376ExactAddressBlock cert (e j).1,
    hzero, ?_⟩
  intro j
  exact mme_CW_2376_exact_address_block_restrict_profile_core
    cert m (e j).1
