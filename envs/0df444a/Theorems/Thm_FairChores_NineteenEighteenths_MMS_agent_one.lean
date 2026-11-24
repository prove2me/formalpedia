-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_one
-- name    : FairChores.NineteenEighteenths.MMS_agent_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:37.675844+00:00
-- url     : https://prove2.me/theorems/58dd6b8d-26fa-4eee-b757-8418e24db5b0
-- title:
--   Nineteen Eighteenths: MMS agent one
-- statement:
--   Agent `1`'s maximin share is `360`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L143-L181
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L143-L181

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores

theorem FairChores.NineteenEighteenths.MMS_agent_one {lam : ℝ} (hlam : 2 ≤ lam) :
    MMS 3 (instC lam 1) (instP lam) = 360 := by sorry
