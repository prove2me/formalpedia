-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_score_start
-- name    : DeletionCode.Recovery.State.score_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:46.292136+00:00
-- url     : https://prove2.me/theorems/96f3aec5-48ea-4020-8d7f-15b24e61425f
-- title:
--   State: score start
-- statement:
--   The State construction uses the score start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L256-L277
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L256-L277

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
open DeletionCode.Recovery.State

theorem DeletionCode.Recovery.State.score_start (s : State B) (b : B) (w : Slot)
    (hb : ¬ s.Started b) : (s.start b w).score = s.score + 1 := by sorry
