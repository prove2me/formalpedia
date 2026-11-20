-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_bubble_spectrum
-- name    : DeletionCode.BubbleCatalogue.bubble_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:33.616972+00:00
-- url     : https://prove2.me/theorems/ed204244-0a76-464f-a244-0ba6a173f1f5
-- title:
--   Bubble Catalogue: bubble spectrum
-- statement:
--   The Bubble Catalogue construction uses the bubble spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L69-L81
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L69-L81

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.bubble_spectrum {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) :
    bubbleSpectrum (editedFamily words rank).family (windowLength k) b =
      wordSpectrum (listLetters (words b).positiveWord) (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord) (words b).negativeWord.length (windowLength k) := by sorry
