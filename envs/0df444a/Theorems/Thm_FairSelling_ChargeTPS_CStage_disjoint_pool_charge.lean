-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_charge
-- name    : FairSelling.ChargeTPS.CStage.disjoint_pool_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:31:20.710126+00:00
-- url     : https://prove2.me/theorems/f0c72e18-266c-41af-b37f-edcf191549ed
-- title:
--   CStage: disjoint pool charge
-- statement:
--   The CStage construction uses the disjoint pool charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L73-L76
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L73-L76

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.ChargeTPS.CStage

theorem FairSelling.ChargeTPS.CStage.disjoint_pool_charge (s : CStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) := by sorry
