-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_fcC_total
-- name    : FairChores.FeigeNorkinChores.fcC_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:00.761598+00:00
-- url     : https://prove2.me/theorems/693327b1-0a68-4232-ba70-0252c10df730
-- title:
--   Feige Norkin Chores: fc C total
-- statement:
--   The total cost of all chores for agent `C` is `1080`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L135-L135
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L135-L135

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.fcC_total : (∑ j, fcC j) = 1080 := by sorry
