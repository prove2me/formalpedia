-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_eight_mul_choose_le_pow
-- name    : DeletionCode.UniqueWordParameters.eight_mul_choose_le_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:04:16.383797+00:00
-- url     : https://prove2.me/theorems/bf7bef8f-c03d-49d4-8808-a545995996ae
-- title:
--   Unique Word Parameters: eight mul choose le pow
-- statement:
--   An exact natural-number form of the paper's collision fraction bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L62-L65
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L62-L65

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.eight_mul_choose_le_pow (n : ℕ) : 8 * n.choose 2 ≤ 2 ^ uniquenessLength n := by sorry
