-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_uniquenessLength_eq_ceil
-- name    : DeletionCode.UniqueWordParameters.uniquenessLength_eq_ceil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:48.624174+00:00
-- url     : https://prove2.me/theorems/0f177b15-ac24-4044-833c-00620812f0e4
-- title:
--   Unique Word Parameters: uniqueness Length eq ceil
-- statement:
--   For positive n, the natural ceiling is the ordinary integer ceiling
--   appearing in the manuscript; the logarithm is nonnegative.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L36-L41
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L36-L41

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.uniquenessLength_eq_ceil (n : ℕ) (hn : 1 ≤ n) :
    (uniquenessLength n : ℤ) = 2 * ⌈Real.logb 2 (n : ℝ)⌉ + 2 := by sorry
