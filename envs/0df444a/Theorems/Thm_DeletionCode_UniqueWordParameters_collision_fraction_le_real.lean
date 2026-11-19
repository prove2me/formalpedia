-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_collision_fraction_le_real
-- name    : DeletionCode.UniqueWordParameters.collision_fraction_le_real
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:41:46.406263+00:00
-- url     : https://prove2.me/theorems/899ceeff-a874-40de-a33e-b8033d42fc90
-- title:
--   Unique Word Parameters: collision fraction le real
-- statement:
--   The Unique Word Parameters construction uses the collision fraction le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L76-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L76-L82

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.collision_fraction_le_real (n : ℕ) :
    (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n ≤ 1 / 8 := by sorry
