-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_family_vertex
-- name    : DeletionCode.BubbleCatalogue.family_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:37.27033+00:00
-- url     : https://prove2.me/theorems/52086633-33a5-40c9-8d18-23104a477cde
-- title:
--   Bubble Catalogue: family vertex
-- statement:
--   The Bubble Catalogue construction uses the family vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L51-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L51-L56

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.family_vertex {B : Type*} {k : ℕ} (words : B → BubbleWord k) (rank : B → ℕ)
    (b : B) (side : Bool) (i : ℕ) :
    SupportComponents.vertex (editedFamily words rank).family (windowLength k) b side i =
      SpectrumPath.vertexAt (listLetters (pathWord (words b) side)) (windowLength k) i := by sorry
