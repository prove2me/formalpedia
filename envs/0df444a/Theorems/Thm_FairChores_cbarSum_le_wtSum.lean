-- Prove2me | Theorems.Thm_FairChores_cbarSum_le_wtSum
-- name    : FairChores.cbarSum_le_wtSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:37.942433+00:00
-- url     : https://prove2.me/theorems/f56f64fd-ee42-4be8-af83-c78b961512f8
-- title:
--   Fair Chores: cbar Sum le wt Sum
-- statement:
--   The Fair Chores construction uses the cbar Sum le wt Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L255-L256
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L255-L256

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_le_wtSum (A : Finset T) : cbarSum c p A ≤ wtSum c p mu A := by sorry
