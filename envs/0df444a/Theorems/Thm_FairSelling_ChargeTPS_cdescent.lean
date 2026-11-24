-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cdescent
-- name    : FairSelling.ChargeTPS.cdescent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:27.881501+00:00
-- url     : https://prove2.me/theorems/e5e40d01-00c0-4b51-88e6-baacc267b107
-- title:
--   Charge TPS: cdescent
-- statement:
--   The descent: every good charged stage can be completed to one in which every agent is
--   served.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L401-L421
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L401-L421

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
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.ChargeTPS.cdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : CImprovementStep v p eps) :
    ∀ (c : ℕ) (s : CStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
