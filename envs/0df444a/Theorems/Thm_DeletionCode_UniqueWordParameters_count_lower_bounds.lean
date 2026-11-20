-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_count_lower_bounds
-- name    : DeletionCode.UniqueWordParameters.count_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:53.277989+00:00
-- url     : https://prove2.me/theorems/c5e66981-8734-47c8-a704-21e1e2a43a80
-- title:
--   Unique Word Parameters: count lower bounds
-- statement:
--   A finite cardinality satisfying the collision union bound inherits
--   both of the manuscript's concluding lower bounds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L118-L123
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L118-L123

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.count_lower_bounds (n count : ℕ) (hn : 1 ≤ n)
    (hcount : (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n ≤ count) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ count ∧ 2 ^ (n - 1) ≤ count := by sorry
