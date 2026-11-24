-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_soldSet
-- name    : FairSelling.ChargeTPS.CStage.disjoint_pool_soldSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:31.755438+00:00
-- url     : https://prove2.me/theorems/55d2e691-beb0-49e1-ac27-14c39384968a
-- title:
--   CStage: disjoint pool sold Set
-- statement:
--   The CStage construction uses the disjoint pool sold Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L63-L66
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L63-L66

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.ChargeTPS.CStage

theorem FairSelling.ChargeTPS.CStage.disjoint_pool_soldSet (s : CStage G n) : Disjoint s.pool s.soldSet := by sorry
