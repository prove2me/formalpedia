-- Prove2me | Theorems.Thm_FairChores_configC_sum_bound
-- name    : FairChores.configC_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:25.874929+00:00
-- url     : https://prove2.me/theorems/280e8821-1d67-4ffd-a16f-ef1975fa5626
-- title:
--   Fair Chores: config C sum bound
-- statement:
--   From a two-part configuration in which both parts cost at most `M`, the total effective
--   cost of the unsplit chores plus the price of the split chores is at most `2 M`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L179-L200
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L179-L200

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.configC_sum_bound (c p : T → ℝ) (M : ℝ) (A : Fin 2 → Finset T) (s : Finset T)
    (q : Fin 2 → ℝ) (h : ConfigC c p M A s q) :
    cbarSum c p (Finset.univ \ s) + ∑ t ∈ s, p t ≤ 2 * M := by sorry
