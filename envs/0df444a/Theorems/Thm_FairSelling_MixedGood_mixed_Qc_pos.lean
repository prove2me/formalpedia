-- Prove2me | Theorems.Thm_FairSelling_MixedGood_mixed_Qc_pos
-- name    : FairSelling.MixedGood.mixed_Qc_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:49.130545+00:00
-- url     : https://prove2.me/theorems/075dd4a4-f174-419f-97d8-e4dc039f8305
-- title:
--   Mixed Good: mixed Qc pos
-- statement:
--   The slice the moving knife would have to cut at the initial stage is positive: both agents
--   have a positive threshold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L150-L165
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L150-L165

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.mixed_Qc_pos (eps : ℝ) :
    0 < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0 (∅ : Finset (Fin 3)) := by sorry
