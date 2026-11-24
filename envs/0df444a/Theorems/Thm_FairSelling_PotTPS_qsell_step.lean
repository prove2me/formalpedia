-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qsell_step
-- name    : FairSelling.PotTPS.qsell_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:51.758926+00:00
-- url     : https://prove2.me/theorems/95d3d057-c4e9-4f89-83d2-5c6941bbe876
-- title:
--   Pot TPS: qsell step
-- statement:
--   **Selling an expensive pool good and cutting a slice of its proceeds.**  The good `g0` is
--   sold, the claimant receives the least slice `Qc(∅)` of its proceeds that makes somebody claim
--   it, and the rest of the proceeds goes into the **pot of `g0`**, from which further slices of
--   `g0` — and nothing else — may later be cut.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L114-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L114-L140

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPotImp
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PotTPS.qsell_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) (k0 : Fin n) {g0 : G} (hg0 : g0 ∈ s.pool)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g0) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
