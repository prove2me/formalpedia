-- Prove2me | Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_two
-- name    : FairChores.NineteenEighteenths.MMS_agent_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:22:44.608683+00:00
-- url     : https://prove2.me/theorems/608fc190-b128-4709-b681-6afefd171ba8
-- title:
--   Nineteen Eighteenths: MMS agent two
-- statement:
--   Agent `2` is indifferent between performing a chore and paying for it, so all her cost is
--   divisible and her maximin share is her proportional share `360 λ`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L185-L211
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/NineteenEighteenths.lean#L185-L211

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

theorem FairChores.NineteenEighteenths.MMS_agent_two {lam : ℝ} (hlam0 : 0 ≤ lam) :
    MMS 3 (instC lam 2) (instP lam) = 360 * lam := by sorry
