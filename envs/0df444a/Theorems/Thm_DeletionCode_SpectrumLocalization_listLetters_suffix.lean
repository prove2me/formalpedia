-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_suffix
-- name    : DeletionCode.SpectrumLocalization.listLetters_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:34:52.067792+00:00
-- url     : https://prove2.me/theorems/da338a66-4697-40d1-b4d2-1bf95dc29bdc
-- title:
--   Spectrum Localization: list Letters suffix
-- statement:
--   The Spectrum Localization construction uses the list Letters suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L120-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L120-L122

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.listLetters_suffix (x p y : List Bool) (i : ℕ) :
    listLetters (x ++ (p ++ y)) (x.length + p.length + i) = listLetters y i := by sorry
