-- Prove2me | Theorems.Thm_FairChores_cbar_nonneg
-- name    : FairChores.cbar_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:24:35.972208+00:00
-- url     : https://prove2.me/theorems/5b68cc29-a170-45ae-b20e-630f970522e4
-- title:
--   Fair Chores: cbar nonneg
-- statement:
--   The Fair Chores construction uses the cbar nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L84-L85
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L84-L85

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbar_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ cbar c p t := by sorry
