-- Prove2me | Theorems.Thm_FairChores_exists_MMS_two_chores
-- name    : FairChores.exists_MMS_two_chores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:27:29.643911+00:00
-- url     : https://prove2.me/theorems/e6e3f2ad-c907-4dbb-b39f-ecf92ab4f67d
-- title:
--   Fair Chores: exists MMS two chores
-- statement:
--   **Exact MMS for two agents, chores with outsourcing.** There is a feasible outcome in
--   which each of the two agents pays at most her maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L332-L349
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L332-L349

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.exists_MMS_two_chores (c : Fin 2 → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T 2, o.Valid p ∧ ∀ i, cost (c i) o i ≤ MMS 2 (c i) p := by sorry
