-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
-- name    : FairSelling.ChargeTPS.req_eq_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:19:41.297338+00:00
-- url     : https://prove2.me/theorems/d934f44b-ade4-463e-a1e1-a0dd1b8a1cf1
-- title:
--   Charge TPS: req eq thr
-- statement:
--   The Charge TPS construction uses the req eq thr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L59-L61
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L59-L61

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [DecidableEq G]

theorem FairSelling.ChargeTPS.req_eq_thr {s : CStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by sorry
