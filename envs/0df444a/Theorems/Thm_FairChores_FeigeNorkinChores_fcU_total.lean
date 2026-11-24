-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_fcU_total
-- name    : FairChores.FeigeNorkinChores.fcU_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:21:52.713205+00:00
-- url     : https://prove2.me/theorems/807e5d05-00f6-435a-bc1f-0f81b5fab8a3
-- title:
--   Feige Norkin Chores: fc U total
-- statement:
--   The total cost of all chores for agent `U` is `1080`, so her proportional share is
--   `360`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L129-L129
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L129-L129

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.fcU_total : (∑ j, fcU j) = 1080 := by sorry
