-- Prove2me | Theorems.Thm_FairSelling_GeneralTPS_descent_inner
-- name    : FairSelling.GeneralTPS.descent_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:55:46.504327+00:00
-- url     : https://prove2.me/theorems/378058d6-3031-4f7d-8422-28d422bdeb72
-- title:
--   General TPS: descent inner
-- statement:
--   The inner descent: with the number of unserved agents fixed, the total utility increases by
--   at least `ε` at every step and is bounded, so the process cannot go on for ever.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L302-L337
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxGeneral.lean#L302-L337

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

theorem FairSelling.GeneralTPS.descent_inner (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : Stage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
