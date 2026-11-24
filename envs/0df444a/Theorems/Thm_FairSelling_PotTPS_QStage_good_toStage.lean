-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_good_toStage
-- name    : FairSelling.PotTPS.QStage.good_toStage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:35:54.557943+00:00
-- url     : https://prove2.me/theorems/e95492fa-b57d-4df2-ab07-12ff15b3ada1
-- title:
--   QStage: good to Stage
-- statement:
--   **The invariant transfers to the plain bookkeeping.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L483-L511
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L483-L511

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_good_toStage

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.good_toStage (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : (s.toStage).Good v p eps := by sorry
