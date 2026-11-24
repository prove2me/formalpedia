-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pbagfill_step
-- name    : FairSelling.PhaseTPS.pbagfill_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:18.142358+00:00
-- url     : https://prove2.me/theorems/dfbaf456-3077-4951-81a2-acdd76d6191f
-- title:
--   Phase TPS: pbagfill step
-- statement:
--   **The bag-filling step of Algorithm 6.**  When no pool good is expensive for an unserved
--   agent, the pool is filled into a bag, the bag is shrunk to a minimal admissible package, and the
--   package is handed to its claimant; if the claimant already holds a bundle, that bundle is
--   released first (`Unshrink`).  Everything the new owner sells is financed out of its own package —
--   the manuscript's *"sharing is avoided in the bag-filling loop"* — so the release is
--   unconditional.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L187-L294
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L187-L294

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

theorem FairSelling.PhaseTPS.pbagfill_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {P : Finset G} (hPpool : P ⊆ s.pool)
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 s.bank P ∅)
    (hcheap : ∀ g ∈ P, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
