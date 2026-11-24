-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_preq_eq_thr
-- name    : FairSelling.PhaseTPS.preq_eq_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:26:41.619811+00:00
-- url     : https://prove2.me/theorems/5bd25870-facd-427a-991d-fcfeb55c87ad
-- title:
--   Phase TPS: preq eq thr
-- statement:
--   The Phase TPS construction uses the preq eq thr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L75-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L75-L77

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
omit [DecidableEq G]

theorem FairSelling.PhaseTPS.preq_eq_thr {s : PStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by sorry
