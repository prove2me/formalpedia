-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_pathWord_length_ge
-- name    : DeletionCode.BubbleCatalogue.pathWord_length_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:34.752387+00:00
-- url     : https://prove2.me/theorems/c176a68e-917f-4a2d-b847-77da9e8bf8d8
-- title:
--   Bubble Catalogue: path Word length ge
-- statement:
--   The Bubble Catalogue construction uses the path Word length ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L27-L35
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L27-L35

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.pathWord_length_ge {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    windowLength k ≤ (pathWord bubble side).length := by sorry
