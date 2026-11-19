-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_delete_longWord
-- name    : DeletionCode.CatalogueWords.BubbleWord.delete_longWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:38.222355+00:00
-- url     : https://prove2.me/theorems/8f52fbbc-1827-4996-94fc-92c536f15830
-- title:
--   Bubble Word: delete long Word
-- statement:
--   The finite-word edit identity also holds for the complete padded functions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L122-L124
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L122-L124

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.delete_longWord (bubble : BubbleWord k) :
    deleteAt (listLetters bubble.longWord) (editOffset k) = listLetters bubble.shortWord := by sorry
