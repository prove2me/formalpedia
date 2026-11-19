-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_negativeWord_semantics
-- name    : DeletionCode.CatalogueWords.BubbleWord.negativeWord_semantics
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:36.809359+00:00
-- url     : https://prove2.me/theorems/52df1a05-52b2-4c49-b6ca-ae7d5778de76
-- title:
--   Bubble Word: negative Word semantics
-- statement:
--   The Bubble Word construction uses the negative Word semantics property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L126-L131
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L126-L131

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.negativeWord_semantics (bubble : BubbleWord k) :
    listLetters bubble.negativeWord =
      negativePath k bubble.header (listLetters bubble.longWord) := by sorry
