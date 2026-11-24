-- Prove2me | Theorems.Thm_FairChores_cbarSum_nonneg
-- name    : FairChores.cbarSum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:14.35904+00:00
-- url     : https://prove2.me/theorems/a7d5d3d8-9e63-41c4-ab5c-406d41ff49d6
-- title:
--   Fair Chores: cbar Sum nonneg
-- statement:
--   The Fair Chores construction uses the cbar Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L94-L96
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L94-L96

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ cbarSum c p A := by sorry
