-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_collision_fraction_le
-- name    : DeletionCode.UniqueWordParameters.collision_fraction_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:41:46.374588+00:00
-- url     : https://prove2.me/theorems/9db79caa-04ee-497a-9475-4a8cc612a4b6
-- title:
--   Unique Word Parameters: collision fraction le
-- statement:
--   The total pairwise collision allowance is at most one eighth.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L68-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L68-L74

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.collision_fraction_le (n : ℕ) :
    (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n ≤ 1 / 8 := by sorry
