-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_pathWord_length
-- name    : DeletionCode.BubbleCatalogue.pathWord_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:32.385348+00:00
-- url     : https://prove2.me/theorems/c17c16e7-82ba-418e-ac8f-764946a4c88a
-- title:
--   Bubble Catalogue: path Word length
-- statement:
--   The Bubble Catalogue construction uses the path Word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L20-L25
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L20-L25

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.pathWord_length {k : ℕ} (bubble : BubbleWord k) (side : Bool) :
    (pathWord bubble side).length = PathMemory.pathLength k bubble.header side := by sorry
