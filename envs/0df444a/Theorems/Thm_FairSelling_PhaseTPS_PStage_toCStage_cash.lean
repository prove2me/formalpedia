-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
-- name    : FairSelling.PhaseTPS.PStage.toCStage_cash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:46.561235+00:00
-- url     : https://prove2.me/theorems/63392a50-9af2-4321-b411-eae98f938af1
-- title:
--   PStage: to CStage cash
-- statement:
--   The PStage construction uses the to CStage cash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L206-L206
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L206-L206

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

theorem FairSelling.PhaseTPS.PStage.toCStage_cash (s : PStage G n) : (s.toCStage).cash = s.cash := by sorry

attribute [defeq] FairSelling.PhaseTPS.PStage.toCStage_cash
