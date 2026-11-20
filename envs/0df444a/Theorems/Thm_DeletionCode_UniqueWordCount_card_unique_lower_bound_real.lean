-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_card_unique_lower_bound_real
-- name    : DeletionCode.UniqueWordCount.card_unique_lower_bound_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:52.404147+00:00
-- url     : https://prove2.me/theorems/648721c4-475c-4c15-9de9-13cd1a7873a4
-- title:
--   Unique Word Count: card unique lower bound real
-- statement:
--   The Unique Word Count construction uses the card unique lower bound real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L147-L154
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L147-L154

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

theorem DeletionCode.UniqueWordCount.card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ≤
      (uniqueWords n k).card := by sorry
