-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordParameters_seven_eighths_le_retained
-- name    : DeletionCode.UniqueWordParameters.seven_eighths_le_retained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:08.139269+00:00
-- url     : https://prove2.me/theorems/01c02c1a-1c0f-4c8e-80b1-0f8184cc4337
-- title:
--   Unique Word Parameters: seven eighths le retained
-- statement:
--   The Unique Word Parameters construction uses the seven eighths le retained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L84-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordParameters.lean#L84-L90

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters

theorem DeletionCode.UniqueWordParameters.seven_eighths_le_retained (n : ℕ) :
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤
      (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n) * (2 : ℚ) ^ n := by sorry
