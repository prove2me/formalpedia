-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_append_right
-- name    : DeletionCode.SpectrumLocalization.listLetters_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:22:48.519757+00:00
-- url     : https://prove2.me/theorems/56e3ec14-89dd-4824-b86d-f4691d73b922
-- title:
--   Spectrum Localization: list Letters append right
-- statement:
--   The Spectrum Localization construction uses the list Letters append right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L110-L114
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L110-L114

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.listLetters_append_right (x y : List Bool) (i : ℕ) :
    listLetters (x ++ y) (x.length + i) = listLetters y i := by sorry
