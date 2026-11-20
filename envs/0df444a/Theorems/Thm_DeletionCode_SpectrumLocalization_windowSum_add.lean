-- Prove2me | Theorems.Thm_DeletionCode_SpectrumLocalization_windowSum_add
-- name    : DeletionCode.SpectrumLocalization.windowSum_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:34:38.897202+00:00
-- url     : https://prove2.me/theorems/e1ffaa3b-b318-4e25-bd3f-7fe9e033f695
-- title:
--   Spectrum Localization: window Sum add
-- statement:
--   The Spectrum Localization construction uses the window Sum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L40-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumLocalization.lean#L40-L46

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedSupport
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_DeletionCode_SpectrumLocalization
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumLocalization
open Windows SignedSupport CatalogueWords
open scoped BigOperators

theorem DeletionCode.SpectrumLocalization.windowSum_add (x : Letters) (L start a b : ℕ) (g : Gram L) :
    windowSum x L start (a + b) g =
      windowSum x L start a g + windowSum x L (start + a) b g := by sorry
