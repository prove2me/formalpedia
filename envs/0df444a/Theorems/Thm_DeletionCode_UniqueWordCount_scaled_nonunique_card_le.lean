-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_scaled_nonunique_card_le
-- name    : DeletionCode.UniqueWordCount.scaled_nonunique_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:53.20358+00:00
-- url     : https://prove2.me/theorems/6c03e589-68c3-4a1f-a4ca-13f4ec0025d5
-- title:
--   Unique Word Count: scaled nonunique card le
-- statement:
--   The Unique Word Count construction uses the scaled nonunique card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L118-L128
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L118-L128

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

theorem DeletionCode.UniqueWordCount.scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords n k).card * 2 ^ k ≤ n.choose 2 * 2 ^ n := by sorry
