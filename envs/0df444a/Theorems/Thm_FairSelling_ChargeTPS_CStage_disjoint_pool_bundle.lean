-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_bundle
-- name    : FairSelling.ChargeTPS.CStage.disjoint_pool_bundle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:01.415227+00:00
-- url     : https://prove2.me/theorems/4b7341e8-0f6a-44c0-9b84-8f21ca75584b
-- title:
--   CStage: disjoint pool bundle
-- statement:
--   The CStage construction uses the disjoint pool bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L68-L71
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L68-L71

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.ChargeTPS.CStage

theorem FairSelling.ChargeTPS.CStage.disjoint_pool_bundle (s : CStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by sorry
