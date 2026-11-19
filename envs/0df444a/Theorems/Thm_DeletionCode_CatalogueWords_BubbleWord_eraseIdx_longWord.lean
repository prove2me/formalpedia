-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_eraseIdx_longWord
-- name    : DeletionCode.CatalogueWords.BubbleWord.eraseIdx_longWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:20:45.141583+00:00
-- url     : https://prove2.me/theorems/caad0af5-efc9-4085-b21e-9d1c67c8ef95
-- title:
--   Bubble Word: erase Idx long Word
-- statement:
--   Removing the indicated run bit gives exactly the shorter grammar word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L111-L119
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L111-L119

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.eraseIdx_longWord (bubble : BubbleWord k) :
    bubble.longWord.eraseIdx (editOffset k) = bubble.shortWord := by sorry
