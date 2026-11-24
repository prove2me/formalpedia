-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pdescent
-- name    : FairSelling.PhaseTPS.pdescent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:09.915725+00:00
-- url     : https://prove2.me/theorems/699658e6-8ee5-4d34-bce1-2197ba5e37cc
-- title:
--   Phase TPS: pdescent
-- statement:
--   Every good stage can be completed to one in which every agent is served.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L440-L460
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L440-L460

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.pdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : PImprovementStep v p eps) :
    ∀ (c : ℕ) (s : PStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
