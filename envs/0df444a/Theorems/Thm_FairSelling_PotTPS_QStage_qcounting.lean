-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_qcounting
-- name    : FairSelling.PotTPS.QStage.qcounting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:43:22.984824+00:00
-- url     : https://prove2.me/theorems/331809f2-8ba4-463b-a189-6e97c014b797
-- title:
--   QStage: qcounting
-- statement:
--   **The accounting theorem.**  The per-agent cost bound implies the counting invariant of
--   Algorithm 4, with the pots of the cut goods deducted from the bank — each of them capped at the
--   threshold of the agent the invariant is stated for.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L363-L460
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L363-L460

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
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.qcounting (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    (j : Fin n) (hj : j ∉ s.served) :
    (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool
        + (s.bank - ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p j)) := by sorry
