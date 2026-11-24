-- Prove2me | Theorems.Thm_FairChores_cbarSum_insert
-- name    : FairChores.cbarSum_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:18:00.031153+00:00
-- url     : https://prove2.me/theorems/3700d83a-752e-48fc-bf9e-a92d42ca0be1
-- title:
--   Fair Chores: cbar Sum insert
-- statement:
--   The Fair Chores construction uses the cbar Sum insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L43-L45
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagLemma.lean#L43-L45

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
omit [Fintype T]

theorem FairChores.cbarSum_insert {ci p : T → ℝ} {X : Finset T} {t : T} (ht : t ∉ X) :
    cbarSum ci p (insert t X) = cbar ci p t + cbarSum ci p X := by sorry
