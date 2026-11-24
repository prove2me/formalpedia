-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pimprovementStep
-- name    : FairSelling.PhaseTPS.pimprovementStep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:47:20.00226+00:00
-- url     : https://prove2.me/theorems/c9b03c7b-0711-433e-a8b4-42adc57dad74
-- title:
--   Phase TPS: pimprovement Step
-- statement:
--   **The improvement step of Algorithm 6**, split into the manuscript's cases, in the
--   manuscript's order.
--
--   1. *The large-good loops.*  If some good in the pool is expensive for an agent that is still
--      unserved — its price is above twice that agent's threshold — the moving knife of
--      `pshare_step` sells it and cuts the least slice of the proceeds that somebody claims, the
--      rest staying in the bank for the other agents.  Every bundle handed out here is a slice of
--      the proceeds of a *single* sold good, so several agents may be served out of one good and
--      there are never more goods sold than agents allocated a bundle.  When the good happens to be
--      *pure* this is `plarge_pure_step`, a special case of the moving knife `pmoney_step`, in which
--      nothing is charged to anybody.
--
--   2. *The bag-filling loop.*  Otherwise no pool good is expensive for an unserved agent, and the
--      whole pool can be bag-filled: it is feasible by the counting invariant (`pfeas_pool`), and
--      `pbagfill_step` shrinks it to a package and hands it to its claimant, releasing the
--      claimant's old package if it had one.  Nothing is shared here: everything the new owner sells
--      is financed out of its own package.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L374-L398
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L374-L398

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

theorem FairSelling.PhaseTPS.pimprovementStep (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    PImprovementStep v p eps := by sorry
