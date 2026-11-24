-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_charge_subset
-- name    : FairSelling.PhaseTPS.PStage.charge_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:41:56.472821+00:00
-- url     : https://prove2.me/theorems/d62662c5-d45b-4e8d-be5f-8bb681aee3e9
-- title:
--   PStage: charge subset
-- statement:
--   The PStage construction uses the charge subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L213-L219
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L213-L219

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

theorem FairSelling.PhaseTPS.PStage.charge_subset (s : PStage G n) (i : Fin n) : (s.toCStage).charge i ⊆ s.charge i := by sorry
