-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length
-- name    : DeletionCode.CatalogueWords.BubbleWord.shortWord_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:36.176059+00:00
-- url     : https://prove2.me/theorems/5edb668c-311b-4513-9f6e-5c22929f600b
-- title:
--   Bubble Word: short Word length
-- statement:
--   The Bubble Word construction uses the short Word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L68-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L68-L74

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.shortWord_length (bubble : BubbleWord k) :
    bubble.shortWord.length = shortLength k bubble.header := by sorry
