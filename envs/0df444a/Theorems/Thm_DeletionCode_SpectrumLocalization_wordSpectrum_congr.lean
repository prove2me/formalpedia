-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_congr
-- name    : DeletionCode.SpectrumLocalization.wordSpectrum_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:26:10.361794+00:00
-- url     : https://prove2.me/theorems/c5379d71-6271-42c4-bd62-71695f3d1938
-- title:
--   Spectrum Localization: word Spectrum congr
-- statement:
--   The Spectrum Localization construction uses the word Spectrum congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L124-L136
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L124-L136

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.wordSpectrum_congr (x y : Letters) (n L : ℕ)
    (h : ∀ i, i < n → x i = y i) (g : Gram L) :
    wordSpectrum x n L g = wordSpectrum y n L g := by sorry
