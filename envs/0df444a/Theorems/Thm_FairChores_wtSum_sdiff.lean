-- Prove2me | Theorems.Thm_FairChores_wtSum_sdiff
-- name    : FairChores.wtSum_sdiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:16:54.845713+00:00
-- url     : https://prove2.me/theorems/7e401b17-7310-472b-bf93-1d9757b71f39
-- title:
--   Fair Chores: wt Sum sdiff
-- statement:
--   The Fair Chores construction uses the wt Sum sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L264-L267
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L264-L267

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T]

theorem FairChores.wtSum_sdiff {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu B = wtSum c p mu (B \ A) + wtSum c p mu A := by sorry
