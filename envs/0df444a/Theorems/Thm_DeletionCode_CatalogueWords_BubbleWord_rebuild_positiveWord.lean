-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_rebuild_positiveWord
-- name    : DeletionCode.CatalogueWords.BubbleWord.rebuild_positiveWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:04:52.332177+00:00
-- url     : https://prove2.me/theorems/c2f01d0a-f302-4fe8-b16c-ced838f0552d
-- title:
--   Bubble Word: rebuild positive Word
-- statement:
--   Rebuilding from the grammar's negative word recovers the grammar's positive word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L141-L145
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L141-L145

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.rebuild_positiveWord (bubble : BubbleWord k) :
    rebuildPositive k bubble.header (listLetters bubble.negativeWord) =
      listLetters bubble.positiveWord := by sorry
