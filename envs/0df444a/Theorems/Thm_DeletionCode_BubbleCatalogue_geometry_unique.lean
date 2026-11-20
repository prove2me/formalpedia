-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_geometry_unique
-- name    : DeletionCode.BubbleCatalogue.geometry_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:27.741822+00:00
-- url     : https://prove2.me/theorems/7d68c2ee-eed7-4978-853a-b0b876c05771
-- title:
--   Bubble Catalogue: geometry unique
-- statement:
--   The Bubble Catalogue construction uses the geometry unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L93-L117
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L93-L117

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.geometry_unique {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble)
    (side : Bool) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (hj : j + (windowLength k - 1) ≤ (pathWord bubble side).length)
    (heq : SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters (pathWord bubble side)) (windowLength k) j) : i = j := by sorry
