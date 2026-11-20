-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_card_uniqueWords_of_length_lt
-- name    : DeletionCode.UniqueWordCount.card_uniqueWords_of_length_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:37.033152+00:00
-- url     : https://prove2.me/theorems/3233c13f-2c46-40ad-b0a6-ee516a46d921
-- title:
--   Unique Word Count: card unique Words of length lt
-- statement:
--   The Unique Word Count construction uses the card unique Words of length lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L79-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L79-L82

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DeletionCode_UniqueWordCount
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable

theorem DeletionCode.UniqueWordCount.card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords n k).card = 2 ^ n := by sorry
