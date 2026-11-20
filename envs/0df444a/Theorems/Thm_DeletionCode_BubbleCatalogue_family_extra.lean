-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_family_extra
-- name    : DeletionCode.BubbleCatalogue.family_extra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:29.368481+00:00
-- url     : https://prove2.me/theorems/8df2ce59-1fa5-4364-8c18-b1db50c932c0
-- title:
--   Bubble Catalogue: family extra
-- statement:
--   The Bubble Catalogue construction uses the family extra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L44-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L44-L49

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.family_extra {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) :
    (editedFamily words rank).family.extra b side =
      (pathWord (words b) side).length - windowLength k := by sorry
