-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pshare_step
-- name    : FairSelling.PhaseTPS.pshare_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:19.325974+00:00
-- url     : https://prove2.me/theorems/77529d0e-04e6-41c8-8c11-4be00bd24adb
-- title:
--   Phase TPS: pshare step
-- statement:
--   **The moving knife on a *shared* good** — the manuscript's price loop for a good whose price
--   exceeds the threshold of some unserved agent but which is *not* pure.
--
--   The good `g` is sold and the claimant receives the least slice `Qc(∅)` of the proceeds that
--   makes somebody claim it; the rest of the proceeds stays in the bank, free for the other agents,
--   so that several agents end up being served out of the one sold good.  This is the *sharing* the
--   manuscript allows in the large-good loops (and only there): every bundle handed out is a slice
--   of the proceeds of a **single** sold good, so there are never more goods sold than agents
--   allocated a bundle.
--
--   The good is charged to the claimant (`PStage.ShareOK`), which from then on holds nothing but its
--   slice `q ≤ p g`.  That is exactly what keeps the loss bounded for the agents that are *not*
--   served by the step: by `ChargeTPS.cash_add_saleLoss_le` the whole package costs an unserved
--   agent `j` at most `q + loss_j(g) ≤ TPS_j ≤ 2·τ_j`, however small the slice is and however many
--   agents share the good.
--
--   Sharing is only possible if the claimant is not *already* carrying a shared good; that case is
--   `pcarrier_reassign`, the one step of Algorithm 6 that is left unproved.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L316-L353
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L316-L353

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.pshare_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) (k0 : Fin n)
    {g : G} (hg : g ∈ s.pool)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
