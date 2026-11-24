-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
-- name    : FairSelling.PhaseTPS.PStage.toCStage_resv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:38.944685+00:00
-- url     : https://prove2.me/theorems/ab22b87d-4b57-450b-9581-769eafd3040d
-- title:
--   PStage: to CStage resv
-- statement:
--   The PStage construction uses the to CStage resv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L208-L208
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L208-L208

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
omit [Fintype G]

theorem FairSelling.PhaseTPS.PStage.toCStage_resv (s : PStage G n) : (s.toCStage).resv = s.resv := by sorry

attribute [defeq] FairSelling.PhaseTPS.PStage.toCStage_resv
