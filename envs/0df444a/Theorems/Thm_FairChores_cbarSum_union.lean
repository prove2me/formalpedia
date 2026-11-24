-- Prove2me | Theorems.Thm_FairChores_cbarSum_union
-- name    : FairChores.cbarSum_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:14.546291+00:00
-- url     : https://prove2.me/theorems/1f3426b8-50ec-4b32-8529-7394b9c4406f
-- title:
--   Fair Chores: cbar Sum union
-- statement:
--   The Fair Chores construction uses the cbar Sum union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L46-L48
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L46-L48

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T]

theorem FairChores.cbarSum_union (c p : T → ℝ) {A B : Finset T} (h : Disjoint A B) :
    cbarSum c p (A ∪ B) = cbarSum c p A + cbarSum c p B := by sorry
