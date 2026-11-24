-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qdescent_inner
-- name    : FairSelling.PotTPS.qdescent_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:28.897235+00:00
-- url     : https://prove2.me/theorems/b9994810-ea00-42a7-b1f7-cd3bf7b69c78
-- title:
--   Pot TPS: qdescent inner
-- statement:
--   The inner descent: with the number of unserved agents fixed, the total utility increases by
--   at least `ε` at every step and is bounded.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L566-L601
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L566-L601

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

theorem FairSelling.PotTPS.qdescent_inner (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : QImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : QStage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : QStage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      GeneralTPS.totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by sorry
