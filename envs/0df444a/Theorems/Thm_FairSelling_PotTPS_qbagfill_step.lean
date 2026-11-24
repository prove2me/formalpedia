-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qbagfill_step
-- name    : FairSelling.PotTPS.qbagfill_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:07.851132+00:00
-- url     : https://prove2.me/theorems/89ed3aaa-fe6e-46f3-9e64-8fb00a83bd92
-- title:
--   Pot TPS: qbagfill step
-- statement:
--   **The bag-filling step of Algorithm 6.**  When no pool good is expensive for an unserved
--   agent, the pool is filled into a bag out of the *free* bank, the bag is shrunk to a minimal
--   admissible package, and the package is handed to its claimant; if the claimant already holds a
--   package it is released first (`Unshrink`).  Everything the new owner sells is financed out of
--   its own package.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L149-L247
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L149-L247

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

theorem FairSelling.PotTPS.qbagfill_step (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    (hfeas : CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅)
    (hcheap : ∀ g ∈ s.pool, ∀ j, j ∉ s.served → p g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
