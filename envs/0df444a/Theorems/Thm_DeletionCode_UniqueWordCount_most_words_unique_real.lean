-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_most_words_unique_real
-- name    : DeletionCode.UniqueWordCount.most_words_unique_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:40:08.194018+00:00
-- url     : https://prove2.me/theorems/15523281-0eeb-4c4a-8c3a-6bf0e6dc0f14
-- title:
--   Unique Word Count: most words unique real
-- statement:
--   The Unique Word Count construction uses the most words unique real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L170-L181
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L170-L181

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

theorem DeletionCode.UniqueWordCount.most_words_unique_real (n : ℕ) (hn : 1 ≤ n) :
    let k := 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2
    (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ≤ (uniqueWords n k).card ∧
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤ (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ n ∧
    (2 : ℝ) ^ (n - 1) ≤ (7 / 8 : ℝ) * (2 : ℝ) ^ n := by sorry
