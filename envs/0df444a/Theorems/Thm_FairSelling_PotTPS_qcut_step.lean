-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qcut_step
-- name    : FairSelling.PotTPS.qcut_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:51.663787+00:00
-- url     : https://prove2.me/theorems/f0772118-f925-4261-80e4-20aa81f22a3d
-- title:
--   Pot TPS: qcut step
-- statement:
--   **Cutting a further slice out of an existing pot.**  If the pot of a cut good `g0` is large
--   enough to serve the claimant, the claimant receives a slice of it.  Nothing is sold, and the
--   claimant's old package — if it had one — is released.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L82-L108
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L82-L108

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

theorem FairSelling.PotTPS.qcut_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) (k0 : Fin n) {g0 : G} (hg0 : g0 ∈ s.cutSet)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.pot p g0) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
