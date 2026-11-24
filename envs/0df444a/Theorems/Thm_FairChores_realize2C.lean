-- Prove2me | Theorems.Thm_FairChores_realize2C
-- name    : FairChores.realize2C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:20.352116+00:00
-- url     : https://prove2.me/theorems/b7070677-1a44-4629-8200-87f1a2cff45d
-- title:
--   Fair Chores: realize2 C
-- statement:
--   Realize a two-agent unified assignment (agent `0` handles `B0`, agent `1` handles `B1`,
--   the chores of `F` are forcibly outsourced with the bill split as `r0, r1`) as a feasible
--   outcome with the stated costs.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L205-L226
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L205-L226

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem FairChores.realize2C (c : Fin 2 → T → ℝ) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (B0 B1 F : Finset T) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hcover : F ∪ (B0 ∪ B1) = Finset.univ)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 = ∑ t ∈ F, p t) :
    ∃ o : Outcome T 2, o.Valid p ∧
      cost (c 0) o 0 = cbarSum (c 0) p B0 + r0 ∧
      cost (c 1) o 1 = cbarSum (c 1) p B1 + r1 := by sorry
