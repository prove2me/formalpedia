-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
-- name    : DeletionCode.CatalogueWords.BubbleWord.longWord_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:29.35766+00:00
-- url     : https://prove2.me/theorems/1673a591-8877-422a-be5d-5393bdad02b9
-- title:
--   Bubble Word: long Word length
-- statement:
--   The Bubble Word construction uses the long Word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L60-L66
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L60-L66

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.longWord_length (bubble : BubbleWord k) :
    bubble.longWord.length = longLength k bubble.header := by sorry
