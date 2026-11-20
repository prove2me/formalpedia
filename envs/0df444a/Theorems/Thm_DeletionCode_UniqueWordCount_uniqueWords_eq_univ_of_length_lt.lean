-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_uniqueWords_eq_univ_of_length_lt
-- name    : DeletionCode.UniqueWordCount.uniqueWords_eq_univ_of_length_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:22.886576+00:00
-- url     : https://prove2.me/theorems/611b004b-2cc3-4500-b2c1-9ecb63c94fa4
-- title:
--   Unique Word Count: unique Words eq univ of length lt
-- statement:
--   The Unique Word Count construction uses the unique Words eq univ of length lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L72-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L72-L77

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

theorem DeletionCode.UniqueWordCount.uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords n k = Finset.univ := by sorry
