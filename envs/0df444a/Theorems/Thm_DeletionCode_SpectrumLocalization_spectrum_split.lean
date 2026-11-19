-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_spectrum_split
-- name    : DeletionCode.SpectrumLocalization.spectrum_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:25:52.707816+00:00
-- url     : https://prove2.me/theorems/03e503c4-7d8f-4c65-a7dc-78967714acbd
-- title:
--   Spectrum Localization: spectrum split
-- statement:
--   All windows split at the two ends of the local path's edge interval.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L60-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L60-L68

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.spectrum_split (x : Letters) (a p b L : ℕ) (hp : L ≤ p + 1) (g : Gram L) :
    wordSpectrum x (a + p + b) L g =
      windowSum x L 0 a g + wordSpectrum (fun i => x (a + i)) p L g +
        windowSum x L (a + (p + 1 - L)) b g := by sorry
