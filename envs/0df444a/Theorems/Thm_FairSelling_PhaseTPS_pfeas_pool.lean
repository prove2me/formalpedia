-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pfeas_pool
-- name    : FairSelling.PhaseTPS.pfeas_pool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:07.31086+00:00
-- url     : https://prove2.me/theorems/fc16ef11-7fb3-4a23-b672-b58250562ce1
-- title:
--   Phase TPS: pfeas pool
-- statement:
--   **The pool is feasible**, for a phase-structured stage: this is the counting invariant of
--   Algorithm 4, which the charged bookkeeping derives from the local cost bound.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L81-L85
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L81-L85

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

theorem FairSelling.PhaseTPS.pfeas_pool (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : PStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by sorry
