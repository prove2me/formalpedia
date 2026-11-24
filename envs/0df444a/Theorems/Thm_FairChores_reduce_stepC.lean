-- Prove2me | Theorems.Thm_FairChores_reduce_stepC
-- name    : FairChores.reduce_stepC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:59:30.431718+00:00
-- url     : https://prove2.me/theorems/5fbb7a95-407b-4e1e-b814-926776763e03
-- title:
--   Fair Chores: reduce step C
-- statement:
--   One reduction step: if the split set has at least two chores, one of them can be moved
--   into a group, strictly decreasing the number of split chores while preserving `ConfigC`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L56-L132
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L56-L132

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.reduce_stepC (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (r : ℝ)
    (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ)
    (hcfg : ConfigC c p r A s q) (hcard : 2 ≤ s.card) :
    ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
      ConfigC c p r A' s' q' ∧ s'.card < s.card := by sorry
