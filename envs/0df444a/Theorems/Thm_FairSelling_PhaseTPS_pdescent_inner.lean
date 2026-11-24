-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pdescent_inner
-- name    : FairSelling.PhaseTPS.pdescent_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:01.439118+00:00
-- url     : https://prove2.me/theorems/5064cb81-09b3-4720-a910-cb619a4321eb
-- title:
--   Phase TPS: pdescent inner
-- statement:
--   The inner descent: with the number of unserved agents fixed, the total utility increases by
--   at least `ε` at every step and is bounded.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L402-L437
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L402-L437

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

theorem FairSelling.PhaseTPS.pdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : PImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : PStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : PStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : PStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
