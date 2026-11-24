-- Prove2me | Theorems.Thm_FairChores_wtSum_mono
-- name    : FairChores.wtSum_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:21:09.603266+00:00
-- url     : https://prove2.me/theorems/9bd73f48-9be1-4a2d-a88a-012e991cb36d
-- title:
--   Fair Chores: wt Sum mono
-- statement:
--   The Fair Chores construction uses the wt Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L270-L272
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L270-L272

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.wtSum_mono (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    wtSum c p mu A ≤ wtSum c p mu B := by sorry
