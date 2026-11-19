-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_started_start_mono
-- name    : DeletionCode.Recovery.State.started_start_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:00:33.751212+00:00
-- url     : https://prove2.me/theorems/4b430bbd-42c6-46fe-8844-017d41bc1483
-- title:
--   State: started start mono
-- statement:
--   The State construction uses the started start mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L66-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L66-L72

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

theorem DeletionCode.Recovery.State.started_start_mono (s : State B) (b a : B) (w : Slot)
    (h : s.Started a) : (s.start b w).Started a := by sorry
