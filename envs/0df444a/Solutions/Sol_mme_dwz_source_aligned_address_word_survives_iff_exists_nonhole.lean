-- Prove2me | solution 1 for mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:59:50.551816+00:00
-- url     : https://prove2.me/submissions/75a3f05e-8c12-41a3-b8c1-8a8c39ba8676

import Definitions.Def_mme_dwz_source_aligned_broken_obj

open MME Module

universe u

open MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (W : AddressZWord outer) :
    addressWordSurvives m outer copy W ↔
      ∃ small : DWZTable2StandardForm.UsefulBlock m outer,
        small ∈ copy.nonholes ∧ small.1 = addressFineZ W := by
  constructor
  · rintro ⟨hW, hmem⟩
    exact ⟨addressUsefulBlock m outer W hW, hmem, rfl⟩
  · rintro ⟨small, hmem, hvalue⟩
    have hW : addressWordUseful m outer W := by
      intro s a
      simpa only [addressFineZ, hvalue] using small.2.2 s a
    refine ⟨hW, ?_⟩
    have heq : addressUsefulBlock m outer W hW = small := by
      apply Subtype.ext
      exact hvalue.symm
    simpa only [heq] using hmem
