-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_nonunique_card_le
-- name    : DeletionCode.UniqueWordCount.nonunique_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:34.468808+00:00
-- url     : https://prove2.me/theorems/388083d3-8401-4d2d-b02b-2d8813b664a8
-- title:
--   Unique Word Count: nonunique card le
-- statement:
--   Union bound on the actual nonunique family, counted once per word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L111-L116
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L111-L116

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

theorem DeletionCode.UniqueWordCount.nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords n k).card ≤ n.choose 2 * 2 ^ (n - k) := by sorry
