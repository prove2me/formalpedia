-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_seven_eighths_le_retained_real
-- name    : DeletionCode.UniqueWordParameters.seven_eighths_le_retained_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:41:55.404208+00:00
-- url     : https://prove2.me/theorems/30bf17ab-11e8-4b51-b734-769adf04b18a
-- title:
--   Unique Word Parameters: seven eighths le retained real
-- statement:
--   The Unique Word Parameters construction uses the seven eighths le retained real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L92-L98
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L92-L98

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.seven_eighths_le_retained_real (n : ℕ) :
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      (1 - (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n) * (2 : ℝ) ^ n := by sorry
