-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_charge
-- name    : FairSelling.PhaseTPS.PStage.disjoint_pool_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:12.741062+00:00
-- url     : https://prove2.me/theorems/94ed004d-7501-4994-bd90-d5682da7bc7b
-- title:
--   PStage: disjoint pool charge
-- statement:
--   The PStage construction uses the disjoint pool charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L345-L348
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L345-L348

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_charge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.PStage.disjoint_pool_charge (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) := by sorry
