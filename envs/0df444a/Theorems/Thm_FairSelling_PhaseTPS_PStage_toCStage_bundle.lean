-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
-- name    : FairSelling.PhaseTPS.PStage.toCStage_bundle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:02.28382+00:00
-- url     : https://prove2.me/theorems/bcd42722-802e-4aac-8c17-45a8ff263f8a
-- title:
--   PStage: to CStage bundle
-- statement:
--   The PStage construction uses the to CStage bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L204-L204
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L204-L204

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

theorem FairSelling.PhaseTPS.PStage.toCStage_bundle (s : PStage G n) : (s.toCStage).bundle = s.bundle := by sorry

attribute [defeq] FairSelling.PhaseTPS.PStage.toCStage_bundle
