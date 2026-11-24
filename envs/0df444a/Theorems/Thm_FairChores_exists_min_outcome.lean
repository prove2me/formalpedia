-- Prove2me | Theorems.Thm_FairChores_exists_min_outcome
-- name    : FairChores.exists_min_outcome
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:41.045611+00:00
-- url     : https://prove2.me/theorems/388cfc76-cfee-42be-be5e-09e7982ea318
-- title:
--   Fair Chores: exists min outcome
-- statement:
--   There is a feasible outcome minimising the worst-part cost.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L241-L255
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L241-L255

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.exists_min_outcome (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hn : 0 < n) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ o' : Outcome T n, o'.Valid p → maxCost c o ≤ maxCost c o' := by sorry
