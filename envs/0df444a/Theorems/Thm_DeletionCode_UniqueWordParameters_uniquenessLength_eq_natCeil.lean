-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_uniquenessLength_eq_natCeil
-- name    : DeletionCode.UniqueWordParameters.uniquenessLength_eq_natCeil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:02.789222+00:00
-- url     : https://prove2.me/theorems/afb99d53-9e62-4eea-b81f-f37131aebe93
-- title:
--   Unique Word Parameters: uniqueness Length eq nat Ceil
-- statement:
--   Exact agreement with the natural ceiling of the real logarithm.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L27-L32
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L27-L32

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.uniquenessLength_eq_natCeil (n : ℕ) :
    uniquenessLength n = 2 * ⌈Real.logb 2 (n : ℝ)⌉₊ + 2 := by sorry
