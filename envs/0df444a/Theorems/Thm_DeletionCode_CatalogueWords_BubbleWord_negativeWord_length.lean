-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_negativeWord_length
-- name    : DeletionCode.CatalogueWords.BubbleWord.negativeWord_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:26:15.685963+00:00
-- url     : https://prove2.me/theorems/422515b8-ecdf-4c17-be37-98f6dd448fb1
-- title:
--   Bubble Word: negative Word length
-- statement:
--   The Bubble Word construction uses the negative Word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L76-L81
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L76-L81

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.negativeWord_length (bubble : BubbleWord k) :
    bubble.negativeWord.length = negativeLength k bubble.header := by sorry
