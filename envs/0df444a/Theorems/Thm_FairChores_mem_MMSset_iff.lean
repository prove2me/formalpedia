-- Prove2me | Theorems.Thm_FairChores_mem_MMSset_iff
-- name    : FairChores.mem_MMSset_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:10.114075+00:00
-- url     : https://prove2.me/theorems/f27fb9e1-214f-4649-ac28-e4bf443b323f
-- title:
--   Fair Chores: mem MMSset iff
-- statement:
--   The Fair Chores construction uses the mem MMSset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L43-L47
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSPartition.lean#L43-L47

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.mem_MMSset_iff (hn : 0 < n) (c p : T → ℝ) (r : ℝ) :
    r ∈ MMSset n c p ↔ ∃ o : Outcome T n, o.Valid p ∧ maxCost c o ≤ r := by sorry
