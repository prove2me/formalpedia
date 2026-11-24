-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qfeas_pool
-- name    : FairSelling.PotTPS.qfeas_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:43.63442+00:00
-- url     : https://prove2.me/theorems/c79618aa-0109-4706-b360-82e0a4bf2ee3
-- title:
--   Pot TPS: qfeas pool
-- statement:
--   **The pool is feasible for the free bank**, provided every pot is below the threshold of the
--   unserved agent `k0`.  This is the counting invariant `qcounting`: the deduction it makes for the
--   cut goods is capped at `τ`, and when every pot is below `τ` that deduction is exactly the money
--   the pots hold back, so what is left is the free bank.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L47-L75
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotImp.lean#L47-L75

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

theorem FairSelling.PotTPS.qfeas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served)
    (hsmall : ∀ g ∈ s.cutSet, s.pot p g ≤ GeneralTPS.thr v p k0) :
    CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅ := by sorry
