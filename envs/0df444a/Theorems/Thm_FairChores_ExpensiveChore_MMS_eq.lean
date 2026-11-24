-- Prove2me | Theorems.Thm_FairChores_ExpensiveChore_MMS_eq
-- name    : FairChores.ExpensiveChore.MMS_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:42.909923+00:00
-- url     : https://prove2.me/theorems/ccda737a-b17e-4943-a4d2-5abdd2c4b934
-- title:
--   Expensive Chore: MMS eq
-- statement:
--   The maximin share of the instance is `2`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L63-L73
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L63-L73

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore

theorem FairChores.ExpensiveChore.MMS_eq : MMS 3 cc pp = 2 := by sorry
