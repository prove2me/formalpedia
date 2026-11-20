-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_family_path
-- name    : DeletionCode.BubbleCatalogue.family_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:31.373618+00:00
-- url     : https://prove2.me/theorems/a9e44efa-15b8-4c4a-a6b4-6d2551dad2bd
-- title:
--   Bubble Catalogue: family path
-- statement:
--   The Bubble Catalogue construction uses the family path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L37-L42
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L37-L42

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.family_path {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) :
    (editedFamily words rank).family.path b side = listLetters (pathWord (words b) side) := by sorry
