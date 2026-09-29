-- Prove2me | solution 1 for mme_dwz_sourceWord_exact_profile_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:58:52.17915+00:00
-- url     : https://prove2.me/submissions/9cdffb83-c4ee-477d-ad7d-cbe3e1d9d2f8

import Definitions.Def_mme_dwz_global_common_state_broken_copy

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hprofile : ∀ r s,
      Fintype.card {t : Fin (N + 1) // edge r t = s} =
        MME.DWZTable2Counts.component s * m) :
    ∀ r s,
      Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
        MME.DWZTable2Counts.component s * m := by
  intro r s
  let e :
      {t : Fin L //
        MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} ≃
      {t : Fin (N + 1) // edge r t = s} :=
    {
    toFun t := ⟨reindex.symm t.1, by
      simpa only [MME.DWZGlobalCorrelated.sourceWord] using t.2⟩
    invFun t := ⟨reindex t.1, by
      simpa only [MME.DWZGlobalCorrelated.sourceWord,
        Equiv.symm_apply_apply] using t.2⟩
    left_inv t := by
      apply Subtype.ext
      exact reindex.apply_symm_apply t.1
    right_inv t := by
      apply Subtype.ext
      exact reindex.symm_apply_apply t.1
    }
  calc
    Fintype.card
          {t : Fin L //
            MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
        Fintype.card {t : Fin (N + 1) // edge r t = s} :=
      Fintype.card_congr e
    _ = MME.DWZTable2Counts.component s * m := hprofile r s
