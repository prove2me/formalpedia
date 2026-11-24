-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qdescent
-- name    : FairSelling.PotTPS.qdescent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:31.423174+00:00
-- url     : https://prove2.me/theorems/3ba1a538-c223-498c-b777-cded0f82f014
-- title:
--   Pot TPS: qdescent
-- statement:
--   Every good stage can be completed to one in which every agent is served.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L604-L624
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L604-L624

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
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PotTPS.qdescent (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : QImprovementStep v p eps) :
    ∀ (c : ℕ) (s : QStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
