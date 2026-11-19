-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_two_mul_choose_le_square
-- name    : DeletionCode.UniqueWordParameters.two_mul_choose_le_square
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:41:29.910722+00:00
-- url     : https://prove2.me/theorems/590a4155-d763-484a-9b9b-f786e9d8ef04
-- title:
--   Unique Word Parameters: two mul choose le square
-- statement:
--   The Unique Word Parameters construction uses the two mul choose le square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L43-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L43-L47

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.two_mul_choose_le_square (n : ℕ) : 2 * n.choose 2 ≤ n ^ 2 := by sorry
