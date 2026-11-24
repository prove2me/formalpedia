-- Prove2me | Theorems.Thm_FairChores_cbarSum_sdiff
-- name    : FairChores.cbarSum_sdiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:16.654085+00:00
-- url     : https://prove2.me/theorems/fcb140ce-d430-45db-814d-4e6b94c47f49
-- title:
--   Fair Chores: cbar Sum sdiff
-- statement:
--   The Fair Chores construction uses the cbar Sum sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L104-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L104-L107

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T]

theorem FairChores.cbarSum_sdiff (c p : T → ℝ) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p B = cbarSum c p (B \ A) + cbarSum c p A := by sorry
