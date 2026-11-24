-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cdescent_inner
-- name    : FairSelling.ChargeTPS.cdescent_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:13.99745+00:00
-- url     : https://prove2.me/theorems/ef169475-51bf-41cb-b914-f9b18031ba08
-- title:
--   Charge TPS: cdescent inner
-- statement:
--   The inner descent: with the number of unserved agents fixed, the total utility increases by
--   at least `ε` at every step and is bounded, so the process cannot go on for ever.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L362-L397
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxCharge.lean#L362-L397

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

theorem FairSelling.ChargeTPS.cdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : CImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : CStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : CStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : CStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
