-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_fnU_total
-- name    : FairSelling.FeigeNorkin.fnU_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:13.726373+00:00
-- url     : https://prove2.me/theorems/f0daface-9969-46a7-bf3b-9f0dd0b56789
-- title:
--   Feige Norkin: fn U total
-- statement:
--   The total value of all goods for agent `U` is `108`, so her proportional share is `36`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L145-L145
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L145-L145

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.fnU_total : (∑ j, fnU j) = 108 := by sorry
