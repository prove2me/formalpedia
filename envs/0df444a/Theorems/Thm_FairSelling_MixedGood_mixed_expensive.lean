-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixed_expensive
-- name    : FairSelling.MixedGood.mixed_expensive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:23.937494+00:00
-- url     : https://prove2.me/theorems/7b60d401-0d81-47ba-b408-cad2de901c0b
-- title:
--   Mixed Good: mixed expensive
-- statement:
--   **The first good is expensive for agent `0`.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L112-L115
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L112-L115

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixed_expensive : 2 * GeneralTPS.thr mv mp 0 < mp 0 := by sorry
