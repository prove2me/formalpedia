-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_complete_start
-- name    : DeletionCode.Recovery.State.complete_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:36.255784+00:00
-- url     : https://prove2.me/theorems/c6425f56-c355-4405-9e46-3b350ba7e2ff
-- title:
--   State: complete start
-- statement:
--   The State construction uses the complete start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L74-L75
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L74-L75

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State

theorem DeletionCode.Recovery.State.complete_start (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.start b w).Complete a := by sorry
