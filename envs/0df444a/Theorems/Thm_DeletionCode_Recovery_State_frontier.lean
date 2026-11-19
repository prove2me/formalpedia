-- Prove2me | Theorems.Thm_DeletionCode_Recovery_State_frontier
-- name    : DeletionCode.Recovery.State.frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:03.464439+00:00
-- url     : https://prove2.me/theorems/68139fa9-0dd0-43b3-bb88-fc0b2b8bbfcc
-- title:
--   State: frontier
-- statement:
--   An incomplete started bubble has a ready unfilled window.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L113-L145
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/Recovery.lean#L113-L145

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

theorem DeletionCode.Recovery.State.frontier (s : State B) (b : B)
    (hb : s.Started b) (hi : ¬ s.Complete b) :
    ∃ w, s.Ready b w ∧ ¬ s.Done b w := by sorry
