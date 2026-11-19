-- Prove2me | Theorems.Thm_DeletionCode_Recovery_initial_wellFormed
-- name    : DeletionCode.Recovery.initial_wellFormed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:05.173206+00:00
-- url     : https://prove2.me/theorems/cd9d4d9e-4ec4-457a-922e-85a2a4303ee7
-- title:
--   Recovery: initial well Formed
-- statement:
--   The Recovery construction uses the initial well Formed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L334-L341
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L334-L341

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]

theorem DeletionCode.Recovery.initial_wellFormed (M : Data B) : (initial M).WellFormed M := by sorry
