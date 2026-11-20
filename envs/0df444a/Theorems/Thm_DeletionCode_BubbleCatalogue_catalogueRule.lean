-- Prove2me | Theorems.Thm_DeletionCode_BubbleCatalogue_catalogueRule
-- name    : DeletionCode.BubbleCatalogue.catalogueRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:25.883449+00:00
-- url     : https://prove2.me/theorems/52081cdc-6557-4b0c-9be8-5265c679380e
-- title:
--   Bubble Catalogue: catalogue Rule
-- statement:
--   The signed catalogue constructor with all word-level obligations explicit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L205-L227
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleCatalogue.lean#L205-L227

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators

theorem DeletionCode.BubbleCatalogue.catalogueRule {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (hboundary : ∀ b, (words b).left.getLast? = some (!(words b).bit) ∧
      (words b).right.head? = some (!(words b).bit))
    (hgeometry : ∀ b, Geometry (words b))
    (hdisjoint : ∀ a b : Fin (2 * t), a ≠ b → ∀ sa sb i j,
      i + (windowLength k - 1) ≤ (pathWord (words a) sa).length →
      j + (windowLength k - 1) ≤ (pathWord (words b) sb).length →
      SpectrumPath.vertexAt (listLetters (pathWord (words a) sa)) (windowLength k) i ≠
        SpectrumPath.vertexAt (listLetters (pathWord (words b) sb)) (windowLength k) j)
    (hdel : (Finset.univ.filter (fun b => (words b).orientation = .deletion)).card = t)
    (hins : (Finset.univ.filter (fun b => (words b).orientation = .insertion)).card = t) :
    ConnectedBlocks.CatalogueRule t k
      (∑ b, (wordSpectrum (listLetters (words b).positiveWord)
        (words b).positiveWord.length (windowLength k) -
        wordSpectrum (listLetters (words b).negativeWord)
          (words b).negativeWord.length (windowLength k))) := by sorry
