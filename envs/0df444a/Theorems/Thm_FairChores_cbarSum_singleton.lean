-- Prove2me | Theorems.Thm_FairChores_cbarSum_singleton
-- name    : FairChores.cbarSum_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:21:04.294566+00:00
-- url     : https://prove2.me/theorems/5022bbec-5c88-419d-b420-044c197a97fd
-- title:
--   Fair Chores: cbar Sum singleton
-- statement:
--   The Fair Chores construction uses the cbar Sum singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L51-L52
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L51-L52

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbarSum_singleton (c p : T → ℝ) (t : T) : cbarSum c p ({t} : Finset T) = cbar c p t := by sorry
