-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_zero
-- name    : FairChores.NineteenEighteenths.MMS_agent_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:43.658527+00:00
-- url     : https://prove2.me/theorems/9b63187d-9e8d-423a-bd63-c14da1214c74
-- title:
--   Nineteen Eighteenths: MMS agent zero
-- statement:
--   Agent `0`'s maximin share is `360` (that is, `18` before scaling).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L100-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L100-L140

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

theorem FairChores.NineteenEighteenths.MMS_agent_zero {lam : ℝ} (hlam : 2 ≤ lam) :
    MMS 3 (instC lam 0) (instP lam) = 360 := by sorry
