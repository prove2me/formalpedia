-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_thr_le_req
-- name    : FairSelling.PotTPS.QStage.thr_le_req
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:23.323271+00:00
-- url     : https://prove2.me/theorems/356ce102-bdf8-48f0-9fa9-c5f26bd823e9
-- title:
--   QStage: thr le req
-- statement:
--   The threshold never exceeds the requirement.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L300-L305
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L300-L305

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.thr_le_req (heps : 0 ≤ eps) {s : QStage G n} (hs : s.Good v p eps) (j : Fin n) :
    GeneralTPS.thr v p j ≤ s.req v p eps j := by sorry
