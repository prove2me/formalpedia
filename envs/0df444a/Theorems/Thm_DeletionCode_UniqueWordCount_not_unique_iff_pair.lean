-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_not_unique_iff_pair
-- name    : DeletionCode.UniqueWordCount.not_unique_iff_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:28.751238+00:00
-- url     : https://prove2.me/theorems/a1765996-71ea-4842-9a1b-49ea1434f380
-- title:
--   Unique Word Count: not unique iff pair
-- statement:
--   The Unique Word Count construction uses the not unique iff pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L38-L57
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L38-L57

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

theorem DeletionCode.UniqueWordCount.not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits n) :
    ¬ KUnique (padBits x) n k ↔
      ∃ a b : Fin n, a < b ∧ RepeatedWindow k a b x := by sorry
