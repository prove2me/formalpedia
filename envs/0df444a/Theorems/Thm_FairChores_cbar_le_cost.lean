-- Prove2me | Theorems.Thm_FairChores_cbar_le_cost
-- name    : FairChores.cbar_le_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:39.723831+00:00
-- url     : https://prove2.me/theorems/4977a796-c1ab-47f8-9f1b-f330c5737537
-- title:
--   Fair Chores: cbar le cost
-- statement:
--   The Fair Chores construction uses the cbar le cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L88-L88
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L88-L88

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbar_le_cost (t : T) : cbar c p t ≤ c t := by sorry
