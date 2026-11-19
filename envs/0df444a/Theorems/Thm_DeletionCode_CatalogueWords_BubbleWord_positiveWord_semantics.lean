-- Prove2me | Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_positiveWord_semantics
-- name    : DeletionCode.CatalogueWords.BubbleWord.positiveWord_semantics
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:01.730025+00:00
-- url     : https://prove2.me/theorems/cdf47304-1b22-4c90-962d-83b4e64ad83f
-- title:
--   Bubble Word: positive Word semantics
-- statement:
--   The Bubble Word construction uses the positive Word semantics property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L133-L138
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueWords.lean#L133-L138

import Definitions.Def_DeletionCode_GeneratingModel
import Init.Data.List.Nat.Erase
import Definitions.Def_DeletionCode_CatalogueWords
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueWords
open Windows HeaderRecovery GeneratingModel
open DeletionCode.CatalogueWords.BubbleWord
variable {k : ℕ}

theorem DeletionCode.CatalogueWords.BubbleWord.positiveWord_semantics (bubble : BubbleWord k) :
    listLetters bubble.positiveWord =
      positivePath k bubble.header (listLetters bubble.longWord) := by sorry
