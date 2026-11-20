-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_most_words_unique
-- name    : DeletionCode.UniqueWordCount.most_words_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:59.890922+00:00
-- url     : https://prove2.me/theorems/36620691-1421-4f35-a4ae-eddd146b1409
-- title:
--   Unique Word Count: most words unique
-- statement:
--   Complete lemma `lem:family`: the paper's parameter retains at least
--   seven eighths of all n-bit words, and hence at least 2^(n-1) words.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L158-L168
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L158-L168

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

theorem DeletionCode.UniqueWordCount.most_words_unique (n : ℕ) (hn : 1 ≤ n) :
    let k := UniqueWordParameters.uniquenessLength n
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤ (uniqueWords n k).card ∧
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ∧
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by sorry
