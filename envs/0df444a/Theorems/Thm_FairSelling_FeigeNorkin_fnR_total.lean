-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_fnR_total
-- name    : FairSelling.FeigeNorkin.fnR_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:35.657803+00:00
-- url     : https://prove2.me/theorems/2e6e5b13-6406-424a-ba49-3142678bd130
-- title:
--   Feige Norkin: fn R total
-- statement:
--   The total value of all goods for agent `R` is `108`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L148-L148
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L148-L148

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.fnR_total : (∑ j, fnR j) = 108 := by sorry
