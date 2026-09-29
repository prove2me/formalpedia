-- Prove2me | solution 1 for mme_dwz_grouped_allowed_words_exists_unique_usefulBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:58:12.673696+00:00
-- url     : https://prove2.me/submissions/db09c45d-99b2-4889-badc-e067f81a5438

import Definitions.Def_mme_dwz_grouped_allowed_component_words
import Theorems.Thm_mme_dwz_grouped_allowed_words_useful_certificate

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (W : GroupedAllowedWords.{u} m) :
    ∃! small : MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)),
      small.1 = groupedFineZ W := by
  let h := mme_dwz_grouped_allowed_words_useful_certificate m W
  let small : MME.DWZTable2StandardForm.UsefulBlock m
      (groupedOuter (m := m)) := ⟨groupedFineZ W, h⟩
  refine ⟨small, rfl, ?_⟩
  intro other hother
  apply Subtype.ext
  exact hother
