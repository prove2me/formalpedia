-- Prove2me | Theorems.Thm_FairChores_exists_reducedC
-- name    : FairChores.exists_reducedC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:20.811016+00:00
-- url     : https://prove2.me/theorems/49ed289f-557e-46ba-b444-8e2562b5bb19
-- title:
--   Fair Chores: exists reduced C
-- statement:
--   **Lemma 5 for chores, `n = 2`.** Every cost function has an MMS partition into two parts
--   that forcibly outsources at most one chore.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L155-L170
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L155-L170

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.exists_reducedC (c p : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) :
    ∃ (A : Fin 2 → Finset T) (s : Finset T) (q : Fin 2 → ℝ),
      ConfigC c p (MMS 2 c p) A s q ∧ s.card ≤ 1 := by sorry
