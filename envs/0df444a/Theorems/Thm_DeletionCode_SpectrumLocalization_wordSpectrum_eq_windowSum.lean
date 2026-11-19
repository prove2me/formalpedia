-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_eq_windowSum
-- name    : DeletionCode.SpectrumLocalization.wordSpectrum_eq_windowSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:25:31.573048+00:00
-- url     : https://prove2.me/theorems/d60388d3-d8cb-4965-8efc-7000ec5f45d1
-- title:
--   Spectrum Localization: word Spectrum eq window Sum
-- statement:
--   The guarded finite-word spectrum counts exactly the valid start positions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L21-L38
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L21-L38

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.wordSpectrum_eq_windowSum (x : Letters) (n L : ℕ) (hL : L ≤ n + 1)
    (g : Gram L) : wordSpectrum x n L g = windowSum x L 0 (n + 1 - L) g := by sorry
