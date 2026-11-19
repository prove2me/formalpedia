-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_half_words_le_seven_eighths
-- name    : DeletionCode.UniqueWordParameters.half_words_le_seven_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:09.013204+00:00
-- url     : https://prove2.me/theorems/08c4ca39-50db-453b-a4d4-b6c8fe9a8481
-- title:
--   Unique Word Parameters: half words le seven eighths
-- statement:
--   The Unique Word Parameters construction uses the half words le seven eighths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L100-L106
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L100-L106

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.half_words_le_seven_eighths (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by sorry
