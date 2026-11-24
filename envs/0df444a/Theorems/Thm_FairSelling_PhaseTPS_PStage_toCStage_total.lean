-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_total
-- name    : FairSelling.PhaseTPS.PStage.toCStage_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:46:23.048627+00:00
-- url     : https://prove2.me/theorems/71246b3f-1e98-4b5e-8b15-b050bf6a94ba
-- title:
--   PStage: to CStage total
-- statement:
--   The PStage construction uses the to CStage total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L258-L258
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L258-L258

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

theorem FairSelling.PhaseTPS.PStage.toCStage_total (s : PStage G n) : (s.toCStage).total v p = s.total v p := by sorry
