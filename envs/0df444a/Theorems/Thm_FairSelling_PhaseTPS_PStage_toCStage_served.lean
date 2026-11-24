-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
-- name    : FairSelling.PhaseTPS.PStage.toCStage_served
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:22.408834+00:00
-- url     : https://prove2.me/theorems/a2dbdb27-6f30-487c-8d89-408324f66453
-- title:
--   PStage: to CStage served
-- statement:
--   The PStage construction uses the to CStage served property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L202-L202
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L202-L202

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

theorem FairSelling.PhaseTPS.PStage.toCStage_served (s : PStage G n) : (s.toCStage).served = s.served := by sorry

attribute [defeq] FairSelling.PhaseTPS.PStage.toCStage_served
