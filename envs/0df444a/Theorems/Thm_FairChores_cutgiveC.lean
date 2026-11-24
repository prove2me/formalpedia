-- Prove2me | Theorems.Thm_FairChores_cutgiveC
-- name    : FairChores.cutgiveC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:53.815858+00:00
-- url     : https://prove2.me/theorems/38518056-f8b4-49ed-aed8-d90f5131bb4a
-- title:
--   Fair Chores: cutgive C
-- statement:
--   **Cut & Give for chores** (the heart of the two-agent argument). If agent `0` (the
--   *Cutter*) has a canonical MMS partition whose split chore is no more expensive than the
--   Giver's, then there is a feasible outcome in which agent `0` pays at most `MMS0` and agent
--   `1` pays at most `MMS1`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L258-L328
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L258-L328

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.cutgiveC (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (Ac : Fin 2 → Finset T) (sc : Finset T) (qc : Fin 2 → ℝ)
    (hc : ConfigC (c 0) p (MMS 2 (c 0) p) Ac sc qc)
    (sg : Finset T) (hsg : sg.card ≤ 1)
    (hbound : cbarSum (c 1) p (Finset.univ \ sg) + ∑ t ∈ sg, p t ≤ 2 * MMS 2 (c 1) p)
    (hcut : ∑ t ∈ sc, p t ≤ ∑ t ∈ sg, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 ≤ MMS 2 (c 0) p ∧ cost (c 1) o 1 ≤ MMS 2 (c 1) p := by sorry
