-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_mem_uniqueWords
-- name    : DeletionCode.UniqueWordCount.mem_uniqueWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:20.674262+00:00
-- url     : https://prove2.me/theorems/1a61ae81-d373-4cb7-a07c-cf400b9a7fca
-- title:
--   Unique Word Count: mem unique Words
-- statement:
--   The Unique Word Count construction uses the mem unique Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L32-L36
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L32-L36

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

theorem DeletionCode.UniqueWordCount.mem_uniqueWords {n k : ℕ} (x : Bits n) :
    x ∈ uniqueWords n k ↔ FiniteConflictGraph.Unique k x := by sorry
