-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_fcR_total
-- name    : FairChores.FeigeNorkinChores.fcR_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:21:55.26517+00:00
-- url     : https://prove2.me/theorems/285e7f38-3326-45a7-a8d2-28bf1a0c96fb
-- title:
--   Feige Norkin Chores: fc R total
-- statement:
--   The total cost of all chores for agent `R` is `1080`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L132-L132
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L132-L132

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.fcR_total : (∑ j, fcR j) = 1080 := by sorry
