-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixedTPS_zero
-- name    : FairSelling.MixedGood.mixedTPS_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:25.248154+00:00
-- url     : https://prove2.me/theorems/00667eb0-70ea-4ee1-9b11-a292d3dbaeb1
-- title:
--   Mixed Good: mixed TPS zero
-- statement:
--   Agent `0` values nothing, so its truncated proportional share is half the total price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L66-L80
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L66-L80

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixedTPS_zero : TPS 2 (mv 0) mp = 2 := by sorry
