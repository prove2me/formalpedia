-- Prove2me | Theorems.Thm_FairChores_cbarSum_mono
-- name    : FairChores.cbarSum_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:19:18.93281+00:00
-- url     : https://prove2.me/theorems/ce07b325-7184-4e73-913c-61a445c11109
-- title:
--   Fair Chores: cbar Sum mono
-- statement:
--   The Fair Chores construction uses the cbar Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L99-L101
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L99-L101

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_mono (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A B : Finset T} (h : A ⊆ B) :
    cbarSum c p A ≤ cbarSum c p B := by sorry
