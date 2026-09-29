-- Prove2me | solution 1 for mme_CW_2376_induced_family_bigAdd_core_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:29:35.571308+00:00
-- url     : https://prove2.me/submissions/ca82389b-b111-4333-aa37-b5dc51610a7e

import Theorems.Thm_mme_CW_2376_induced_family_selected_blocks
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (fun _ : Fin F.card => cw2376ProfileCore K m))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
        (cw2376ProfileLength m)) := by
  obtain ⟨B, hB, hcore⟩ :=
    mme_CW_2376_induced_family_selected_blocks cert m F hF
  exact TensorObj.Restrict.trans
    (mme_bigAdd_mono_restrict hcore) hB
