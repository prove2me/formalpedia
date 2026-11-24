-- Prove2me | Theorems.Thm_FairChores_wtSum_nonneg
-- name    : FairChores.wtSum_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:49.746372+00:00
-- url     : https://prove2.me/theorems/c6310145-46c2-4d40-8be1-153aeeb53a37
-- title:
--   Fair Chores: wt Sum nonneg
-- statement:
--   The Fair Chores construction uses the wt Sum nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L259-L261
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L259-L261

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.wtSum_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ wtSum c p mu A := by sorry
