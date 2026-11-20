-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_validCatalogue
-- name    : DeletionCode.BubbleCatalogue.validCatalogue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:38.259776+00:00
-- url     : https://prove2.me/theorems/25c974c4-2de3-44ee-b4c0-5b86984ee1ab
-- title:
--   Bubble Catalogue: valid Catalogue
-- statement:
--   The Bubble Catalogue construction uses the valid Catalogue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L140-L189
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L140-L189

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.validCatalogue {k ν : ℕ} (words : Fin ν → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin ν, a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j) :
    ValidCatalogue words (fun _ => (0 : Fin 1)) := by sorry
