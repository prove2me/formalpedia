-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_shift
-- name    : DeletionCode.SpectrumLocalization.windowSum_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:34:36.031242+00:00
-- url     : https://prove2.me/theorems/111ca680-24f8-41e2-b128-0e7063f100f3
-- title:
--   Spectrum Localization: window Sum shift
-- statement:
--   The Spectrum Localization construction uses the window Sum shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L48-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L48-L57

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.windowSum_shift (x : Letters) (L a count : ℕ) (g : Gram L) :
    windowSum x L a count g = windowSum (fun i => x (a + i)) L 0 count g := by sorry
