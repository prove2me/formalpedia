-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qimprovementStep
-- name    : FairSelling.PotTPS.qimprovementStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:16.846508+00:00
-- url     : https://prove2.me/theorems/24092702-29bc-4b7a-8987-36ec5c3b5cc1
-- title:
--   Pot TPS: qimprovement Step
-- statement:
--   **The improvement step of Algorithm 6**, in the manuscript's order.
--
--   1. If some pool good is expensive for an agent that is still unserved, it is sold and a slice of
--      its proceeds is cut for the claimant (`qsell_step`).
--   2. Otherwise, if some pot is already big enough to serve the claimant, a further slice is cut
--      out of it (`qcut_step`).
--   3. Otherwise every pot is below the requirement of every unserved agent, the whole pool is
--      feasible for the free bank (`qfeas_pool`), and one bag-filling step is performed
--      (`qbagfill_step`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L260-L289
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L260-L289

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

theorem FairSelling.PotTPS.qimprovementStep (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    QImprovementStep v p eps := by sorry
