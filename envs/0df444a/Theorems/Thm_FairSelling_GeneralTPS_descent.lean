-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_descent
-- name    : FairSelling.GeneralTPS.descent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:55:51.521358+00:00
-- url     : https://prove2.me/theorems/1154f588-fc0e-4220-869e-f8aaad71b623
-- title:
--   General TPS: descent
-- statement:
--   The descent: every good stage can be completed to a good stage in which every agent is
--   served.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L341-L362
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L341-L362

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.GeneralTPS.descent (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∀ (c : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
