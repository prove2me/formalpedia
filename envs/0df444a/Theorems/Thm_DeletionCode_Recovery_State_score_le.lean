-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_score_le
-- name    : DeletionCode.Recovery.State.score_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:44.511741+00:00
-- url     : https://prove2.me/theorems/ddec93e6-62e6-4187-a2d2-4cdc5141ee89
-- title:
--   State: score le
-- statement:
--   The State construction uses the score le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L248-L254
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L248-L254

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

theorem DeletionCode.Recovery.State.score_le (s : State B) : s.score ≤ 4 * Fintype.card B := by sorry
