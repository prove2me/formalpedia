-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_ready_started
-- name    : DeletionCode.Recovery.State.ready_started
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:34.767214+00:00
-- url     : https://prove2.me/theorems/16aa8f91-5fb7-41be-913e-348a503629b2
-- title:
--   State: ready started
-- statement:
--   The State construction uses the ready started property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L82-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L82-L87

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

theorem DeletionCode.Recovery.State.ready_started (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (h : s.Ready b w) :
    s.Started b := by sorry
