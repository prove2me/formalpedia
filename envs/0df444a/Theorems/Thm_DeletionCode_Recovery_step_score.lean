-- Prove2me | Theorems.Thm_DeletionCode_Recovery_step_score
-- name    : DeletionCode.Recovery.step_score
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:01.435204+00:00
-- url     : https://prove2.me/theorems/24058fa2-15d5-4662-afdf-fbca98e79d00
-- title:
--   Recovery: step score
-- statement:
--   The Recovery construction uses the step score property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L288-L294
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L288-L294

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

theorem DeletionCode.Recovery.step_score (M : Data B) {s s' : State B}
    (h : Step M s s') : s'.score = s.score + 1 := by sorry
