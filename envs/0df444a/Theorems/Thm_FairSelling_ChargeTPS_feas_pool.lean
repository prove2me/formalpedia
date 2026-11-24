-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_feas_pool
-- name    : FairSelling.ChargeTPS.feas_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:36.566259+00:00
-- url     : https://prove2.me/theorems/3f9737df-3de6-469c-9345-3c28a6c921da
-- title:
--   Charge TPS: feas pool
-- statement:
--   **The pool is feasible.**  This is the counting invariant of Algorithm 4, read as a statement
--   about the package consisting of the whole pool: the cheapest cash supplement that makes somebody
--   claim the whole pool can be paid out of the bank.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L98-L123
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L98-L123

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.ChargeTPS.feas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by sorry
