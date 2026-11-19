-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_started_start
-- name    : DeletionCode.Recovery.State.started_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:11.353867+00:00
-- url     : https://prove2.me/theorems/4b8dce4e-e62a-40f4-a632-892d4ad98fbc
-- title:
--   State: started start
-- statement:
--   The State construction uses the started start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L63-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L63-L64

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

theorem DeletionCode.Recovery.State.started_start (s : State B) (b : B) (w : Slot) :
    (s.start b w).Started b := by sorry
