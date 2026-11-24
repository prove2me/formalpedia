-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_sold
-- name    : FairSelling.PhaseTPS.PStage.disjoint_pool_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:04.541939+00:00
-- url     : https://prove2.me/theorems/ba6985dc-4400-4e44-8a92-a04e36c0eb9b
-- title:
--   PStage: disjoint pool sold
-- statement:
--   The PStage construction uses the disjoint pool sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L335-L338
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L335-L338

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

theorem FairSelling.PhaseTPS.PStage.disjoint_pool_sold (s : PStage G n) : Disjoint s.pool s.sold := by sorry
