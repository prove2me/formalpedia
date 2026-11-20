-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_geometry_endpoints
-- name    : DeletionCode.BubbleCatalogue.geometry_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:30.355831+00:00
-- url     : https://prove2.me/theorems/5b1d02a5-ea62-445d-95ae-bbe2cbb66827
-- title:
--   Bubble Catalogue: geometry endpoints
-- statement:
--   The Bubble Catalogue construction uses the geometry endpoints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L119-L138
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L119-L138

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.geometry_endpoints {k : ℕ} (bubble : BubbleWord k) (hg : Geometry bubble) (i j : ℕ)
    (hi : i + (windowLength k - 1) ≤ bubble.negativeWord.length)
    (hj : j + (windowLength k - 1) ≤ bubble.positiveWord.length)
    (heq : SpectrumPath.vertexAt (listLetters bubble.negativeWord) (windowLength k) i =
      SpectrumPath.vertexAt (listLetters bubble.positiveWord) (windowLength k) j) :
    (i = 0 ∧ j = 0) ∨
      (i = bubble.negativeWord.length - windowLength k + 1 ∧
        j = bubble.positiveWord.length - windowLength k + 1) := by sorry
