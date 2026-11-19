-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_left
-- name    : DeletionCode.SpectrumLocalization.listLetters_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:22:38.768984+00:00
-- url     : https://prove2.me/theorems/194dcc89-a9ed-4951-a69e-b029de3cda51
-- title:
--   Spectrum Localization: list Letters append left
-- statement:
--   The Spectrum Localization construction uses the list Letters append left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L105-L108
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L105-L108

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.listLetters_append_left (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    listLetters (x ++ y) i = listLetters x i := by sorry
