-- Prove2me | Theorems.Thm_FairChores_biU_twoC
-- name    : FairChores.biU_twoC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:04.198928+00:00
-- url     : https://prove2.me/theorems/2c8584a2-1d8e-4442-abc3-be5cc76531fa
-- title:
--   Fair Chores: bi U two C
-- statement:
--   The Fair Chores construction uses the bi U two C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L173-L175
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresTwoAgents.lean#L173-L175

import Mathlib
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresTwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
omit [Fintype T]

theorem FairChores.biU_twoC (A : Fin 2 → Finset T) : Finset.univ.biUnion A = A 0 ∪ A 1 := by sorry
