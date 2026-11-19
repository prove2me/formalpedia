-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_start_wellFormed
-- name    : DeletionCode.Recovery.State.start_wellFormed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:40.928954+00:00
-- url     : https://prove2.me/theorems/5848d546-029c-4900-a7c8-ec0cf4456add
-- title:
--   State: start well Formed
-- statement:
--   The State construction uses the start well Formed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L89-L96
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L89-L96

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

theorem DeletionCode.Recovery.State.start_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) :
    WellFormed M (s.start b w) := by sorry
