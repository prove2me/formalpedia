-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_wordSpectrum_eq_pathSpectrum
-- name    : DeletionCode.BubbleCatalogue.wordSpectrum_eq_pathSpectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:34.923514+00:00
-- url     : https://prove2.me/theorems/aebf198b-7cce-4ee6-96d7-e4f50fe83f4c
-- title:
--   Bubble Catalogue: word Spectrum eq path Spectrum
-- statement:
--   The Bubble Catalogue construction uses the word Spectrum eq path Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L58-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L58-L67

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.wordSpectrum_eq_pathSpectrum (x : Letters) (n L : ℕ) (hn : L ≤ n) :
    wordSpectrum x n L = pathSpectrum x L (n - L) := by sorry
