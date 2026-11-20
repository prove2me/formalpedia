-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_family_partition
-- name    : DeletionCode.UniqueWordCount.family_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:23.643294+00:00
-- url     : https://prove2.me/theorems/00f61aed-eee1-434e-b118-f7ca9a29415c
-- title:
--   Unique Word Count: family partition
-- statement:
--   The Unique Word Count construction uses the family partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L59-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L59-L65

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

theorem DeletionCode.UniqueWordCount.family_partition (n k : ℕ) :
    (uniqueWords n k).card + (nonuniqueWords n k).card = 2 ^ n := by sorry
