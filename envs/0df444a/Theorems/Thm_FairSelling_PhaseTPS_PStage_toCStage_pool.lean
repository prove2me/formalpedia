-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_pool
-- name    : FairSelling.PhaseTPS.PStage.toCStage_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:03.14809+00:00
-- url     : https://prove2.me/theorems/f84bfa3d-0e93-4ff9-b1b3-e3e3096b19b3
-- title:
--   PStage: to CStage pool
-- statement:
--   The PStage construction uses the to CStage pool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L249-L252
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L249-L252

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

theorem FairSelling.PhaseTPS.PStage.toCStage_pool (s : PStage G n) : (s.toCStage).pool = s.pool := by sorry
