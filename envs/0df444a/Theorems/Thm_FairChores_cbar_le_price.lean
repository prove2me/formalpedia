-- Prove2me | Theorems.Thm_FairChores_cbar_le_price
-- name    : FairChores.cbar_le_price
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:38.354013+00:00
-- url     : https://prove2.me/theorems/e269983f-89a1-47f4-9218-f91ef785b798
-- title:
--   Fair Chores: cbar le price
-- statement:
--   The Fair Chores construction uses the cbar le price property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L91-L91
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L91-L91

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbar_le_price (t : T) : cbar c p t ≤ p t := by sorry
