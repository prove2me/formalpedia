-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_positiveWord_length
-- name    : DeletionCode.CatalogueWords.BubbleWord.positiveWord_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:26:14.965732+00:00
-- url     : https://prove2.me/theorems/712a60cb-2ecd-45ef-9382-4cefb7b421ce
-- title:
--   Bubble Word: positive Word length
-- statement:
--   The Bubble Word construction uses the positive Word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L83-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L83-L88

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.positiveWord_length (bubble : BubbleWord k) :
    bubble.positiveWord.length = positiveLength k bubble.header := by sorry
