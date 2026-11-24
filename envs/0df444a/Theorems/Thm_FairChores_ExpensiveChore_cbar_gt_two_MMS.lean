-- Prove2me | Theorems.Thm_FairChores_ExpensiveChore_cbar_gt_two_MMS
-- name    : FairChores.ExpensiveChore.cbar_gt_two_MMS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:20:09.887467+00:00
-- url     : https://prove2.me/theorems/a8f9ee96-2b11-43dd-8e70-0fdcc19c70d0
-- title:
--   Expensive Chore: cbar gt two MMS
-- statement:
--   The effective cost of the chore exceeds *twice* the maximin share: with outsourcing, the
--   property that no chore costs more than the MMS fails badly.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L77-L79
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresExamples.lean#L77-L79

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresExamples
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.ExpensiveChore

theorem FairChores.ExpensiveChore.cbar_gt_two_MMS : 2 * MMS 3 cc pp < cbar cc pp 0 := by sorry
