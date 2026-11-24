-- Prove2me | Theorems.Thm_FairChores_cbarSum_le_sum
-- name    : FairChores.cbarSum_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:16:18.406483+00:00
-- url     : https://prove2.me/theorems/5a7ee15f-a9b4-4d3c-a586-68e7008507ff
-- title:
--   Fair Chores: cbar Sum le sum
-- statement:
--   The Fair Chores construction uses the cbar Sum le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L110-L111
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L110-L111

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_le_sum (c p : T → ℝ) (A : Finset T) : cbarSum c p A ≤ ∑ t ∈ A, c t := by sorry
