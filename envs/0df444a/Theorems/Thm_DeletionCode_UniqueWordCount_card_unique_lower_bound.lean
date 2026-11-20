-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_card_unique_lower_bound
-- name    : DeletionCode.UniqueWordCount.card_unique_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:36.797275+00:00
-- url     : https://prove2.me/theorems/5f7c2c57-8870-4138-8957-8fd5fa9b50ae
-- title:
--   Unique Word Count: card unique lower bound
-- statement:
--   The manuscript's union-bound estimate, with the cardinality of the
--   actual k-unique family and no assumed collision-probability premise.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L132-L145
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L132-L145

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

theorem DeletionCode.UniqueWordCount.card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤
      (uniqueWords n k).card := by sorry
