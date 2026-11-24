-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixedThr_pos
-- name    : FairSelling.MixedGood.mixedThr_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:19.551795+00:00
-- url     : https://prove2.me/theorems/344319b4-3b2c-43dd-8ccd-ec9a67854acf
-- title:
--   Mixed Good: mixed Thr pos
-- statement:
--   Both thresholds are positive.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L106-L109
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L106-L109

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixedThr_pos (j : Fin 2) : 0 < GeneralTPS.thr mv mp j := by sorry
