-- Prove2me | Theorems.Thm_FairChores_reduce_to_oneC
-- name    : FairChores.reduce_to_oneC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:03.233772+00:00
-- url     : https://prove2.me/theorems/982285d5-282b-48df-8619-4015c58d439c
-- title:
--   Fair Chores: reduce to one C
-- statement:
--   Iterating `reduce_stepC` we reach a configuration with at most one split chore.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L135-L151
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L135-L151

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.reduce_to_oneC (c p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset T) (s' : Finset T) (q' : Fin 2 → ℝ),
        ConfigC c p r A' s' q' ∧ s'.card ≤ 1 := by sorry
