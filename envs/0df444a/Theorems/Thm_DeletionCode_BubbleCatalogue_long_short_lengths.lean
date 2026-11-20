-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_long_short_lengths
-- name    : DeletionCode.BubbleCatalogue.long_short_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:23.785574+00:00
-- url     : https://prove2.me/theorems/099b439f-4389-4b6c-9116-33e00153bceb
-- title:
--   Bubble Catalogue: long short lengths
-- statement:
--   The Bubble Catalogue construction uses the long short lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L83-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L83-L91

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.long_short_lengths {k : ℕ} (bubble : BubbleWord k) :
    bubble.longWord.length = windowLength k + (windowLength k - bubble.rho) ∧
      bubble.shortWord.length = windowLength k + (windowLength k - bubble.rho - 1) ∧
      1 ≤ windowLength k - bubble.rho := by sorry
