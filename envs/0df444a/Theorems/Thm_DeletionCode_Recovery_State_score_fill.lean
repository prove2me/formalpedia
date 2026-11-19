-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_score_fill
-- name    : DeletionCode.Recovery.State.score_fill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:48.067251+00:00
-- url     : https://prove2.me/theorems/3c28622a-3706-4da5-b035-f9ac47ddd8ee
-- title:
--   State: score fill
-- statement:
--   The State construction uses the score fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L279-L285
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L279-L285

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

theorem DeletionCode.Recovery.State.score_fill (s : State B) (b : B) (w : Slot)
    (hn : ¬ s.Done b w) : (s.fill b w).score = s.score + 1 := by sorry
