-- Prove2me | Theorems.Thm_FairChores_cbar_le_wt
-- name    : FairChores.cbar_le_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:26.044717+00:00
-- url     : https://prove2.me/theorems/6c6ca31a-ba96-4a4e-a0fa-b716afc9f75e
-- title:
--   Fair Chores: cbar le wt
-- statement:
--   The Fair Chores construction uses the cbar le wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L244-L248
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L244-L248

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbar_le_wt (t : T) : cbar c p t ≤ wt c p mu t := by sorry
