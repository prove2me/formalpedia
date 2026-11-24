-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_plarge_pure_step
-- name    : FairSelling.PhaseTPS.plarge_pure_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:47:11.801469+00:00
-- url     : https://prove2.me/theorems/c5ebe1ca-33f8-4266-ace9-7e306467a485
-- title:
--   Phase TPS: plarge pure step
-- statement:
--   **The price loop of Algorithm 6, for a good that is expensive for every unserved agent.**
--   Such a good is *pure*, so the moving-knife step applies to it: it is sold, the claimant receives
--   the least slice of the proceeds that makes somebody claim it, and the rest of the proceeds stays
--   in the bank, available to the other agents.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L152-L177
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L152-L177

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

theorem FairSelling.PhaseTPS.plarge_pure_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n} (hk0 : k0 ∉ s.served)
    {g : G} (hg : g ∈ s.pool)
    (hbig : ∀ j, j ∉ s.served → 2 * GeneralTPS.thr v p j < p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
