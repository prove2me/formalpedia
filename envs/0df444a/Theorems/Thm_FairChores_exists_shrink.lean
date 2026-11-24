-- Prove2me | Theorems.Thm_FairChores_exists_shrink
-- name    : FairChores.exists_shrink
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:11.947786+00:00
-- url     : https://prove2.me/theorems/1e8f18ef-151f-4529-8cc5-2306d7f991d4
-- title:
--   Fair Chores: exists shrink
-- statement:
--   A feasible payment vector may be shrunk to one paying the bill exactly.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L101-L115
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L101-L115

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.exists_shrink {bill : ℝ} (hb : 0 ≤ bill) (m' : Fin n → ℝ) (h0 : ∀ j, 0 ≤ m' j)
    (hs : bill ≤ ∑ j, m' j) :
    ∃ m : Fin n → ℝ, (∀ j, 0 ≤ m j) ∧ (∀ j, m j ≤ m' j) ∧ ∑ j, m j = bill := by sorry
