-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_req
-- name    : FairSelling.PhaseTPS.PStage.toCStage_req
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:46:15.740157+00:00
-- url     : https://prove2.me/theorems/374b6b07-1019-4249-9ba8-38eace4c9865
-- title:
--   PStage: to CStage req
-- statement:
--   The PStage construction uses the to CStage req property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L254-L255
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L254-L255

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.PStage.toCStage_req (s : PStage G n) (j : Fin n) :
    (s.toCStage).req v p eps j = s.req v p eps j := by sorry
