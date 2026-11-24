-- Prove2me | Theorems.Thm_FairChores_wt_nonneg
-- name    : FairChores.wt_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:28.929461+00:00
-- url     : https://prove2.me/theorems/80b9cb4d-044b-41b8-b05a-c1c4573ca846
-- title:
--   Fair Chores: wt nonneg
-- statement:
--   The Fair Chores construction uses the wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L251-L252
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L251-L252

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.wt_nonneg (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ wt c p mu t := by sorry
