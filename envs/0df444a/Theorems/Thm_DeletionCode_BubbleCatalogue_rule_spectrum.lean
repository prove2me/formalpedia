-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_rule_spectrum
-- name    : DeletionCode.BubbleCatalogue.rule_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:31.722929+00:00
-- url     : https://prove2.me/theorems/74b86afc-972d-4320-abd5-bd686671d96f
-- title:
--   Bubble Catalogue: rule spectrum
-- statement:
--   The Bubble Catalogue construction uses the rule spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L191-L202
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L191-L202

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.rule_spectrum {k ν : ℕ} (words : Fin ν → BubbleWord k) (rank : Fin ν → ℕ) :
    ruleSpectrum (editedFamily words rank).family (windowLength k) Finset.univ =
      ∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k)) := by sorry
