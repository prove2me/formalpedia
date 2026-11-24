-- Prove2me | Theorems.Thm_FairChores_ExpensiveChore_exists_chore_cbar_gt_two_MMS
-- name    : FairChores.ExpensiveChore.exists_chore_cbar_gt_two_MMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:25:05.153223+00:00
-- url     : https://prove2.me/theorems/6f3108dc-3bb6-4799-b149-6c7cbfec8311
-- title:
--   Expensive Chore: exists chore cbar gt two MMS
-- statement:
--   Summary of the counterexample.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L82-L84
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L82-L84

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore

theorem FairChores.ExpensiveChore.exists_chore_cbar_gt_two_MMS :
    ∃ (c p : Fin 1 → ℝ) (t : Fin 1), 2 * MMS 3 c p < cbar c p t := by sorry
