-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_half_words_le_card_unique
-- name    : DeletionCode.UniqueWordCount.half_words_le_card_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:32.950424+00:00
-- url     : https://prove2.me/theorems/fe82c2a1-e751-46bc-b6b4-0ca0a03ad5c8
-- title:
--   Unique Word Count: half words le card unique
-- statement:
--   Natural cardinality version used by subsequent code-size estimates.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L184-L187
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L184-L187

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

theorem DeletionCode.UniqueWordCount.half_words_le_card_unique (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ (uniqueWords n (UniqueWordParameters.uniquenessLength n)).card := by sorry
