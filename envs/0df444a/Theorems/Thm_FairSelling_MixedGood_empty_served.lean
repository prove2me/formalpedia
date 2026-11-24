-- Prove2me | Theorems.Thm_FairSelling_MixedGood_empty_served
-- name    : FairSelling.MixedGood.empty_served
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:05.071305+00:00
-- url     : https://prove2.me/theorems/c0575dd0-e952-4b18-8b42-4c167e80a6c3
-- title:
--   Mixed Good: empty served
-- statement:
--   The Mixed Good construction uses the empty served property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L140-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxMixedExample.lean#L140-L140

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.MixedGood

theorem FairSelling.MixedGood.empty_served : (PhaseTPS.emptyPStage (Fin 3) 2).served = (∅ : Finset (Fin 2)) := by sorry
