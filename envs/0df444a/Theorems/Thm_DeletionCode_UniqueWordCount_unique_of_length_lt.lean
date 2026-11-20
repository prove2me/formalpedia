-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_unique_of_length_lt
-- name    : DeletionCode.UniqueWordCount.unique_of_length_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:40.131258+00:00
-- url     : https://prove2.me/theorems/02e5fd81-a8f9-4d9f-b4f2-91a2b26d0893
-- title:
--   Unique Word Count: unique of length lt
-- statement:
--   The Unique Word Count construction uses the unique of length lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L67-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L67-L70

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

theorem DeletionCode.UniqueWordCount.unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits n) :
    KUnique (padBits x) n k := by sorry
