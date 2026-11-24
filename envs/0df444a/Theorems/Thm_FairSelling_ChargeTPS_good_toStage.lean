-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_good_toStage
-- name    : FairSelling.ChargeTPS.good_toStage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:19:37.233887+00:00
-- url     : https://prove2.me/theorems/3472dfb1-745b-4986-bb45-b4b2ee8f3437
-- title:
--   Charge TPS: good to Stage
-- statement:
--   A good charged stage is a good stage in the sense of `TPSSefxGeneral`: the counting
--   invariant of Algorithm 4 is *derived* from the local cost bound.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L286-L318
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L286-L318

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage

theorem FairSelling.ChargeTPS.good_toStage (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) :
    (s.toStage).Good v p eps := by sorry
