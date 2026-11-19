-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_middle
-- name    : DeletionCode.SpectrumLocalization.listLetters_middle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:44.406944+00:00
-- url     : https://prove2.me/theorems/09f2fb24-344b-4d4d-bb8e-ae877a36977f
-- title:
--   Spectrum Localization: list Letters middle
-- statement:
--   The Spectrum Localization construction uses the list Letters middle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L116-L118
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L116-L118

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.listLetters_middle (x p y : List Bool) (i : ℕ) (hi : i < p.length) :
    listLetters (x ++ (p ++ y)) (x.length + i) = listLetters p i := by sorry
