-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_fnC_total
-- name    : FairSelling.FeigeNorkin.fnC_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:44.554684+00:00
-- url     : https://prove2.me/theorems/57069915-df70-40fb-b3a1-c6296f321e3f
-- title:
--   Feige Norkin: fn C total
-- statement:
--   The total value of all goods for agent `C` is `108`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L151-L151
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L151-L151

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.fnC_total : (∑ j, fnC j) = 108 := by sorry
