-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_bundle
-- name    : FairSelling.PhaseTPS.PStage.disjoint_pool_bundle
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:59:32.348439+00:00
-- url     : https://prove2.me/theorems/958b1daf-0cc7-4735-b903-4ee7dc948d92
-- title:
--   PStage: disjoint pool bundle
-- statement:
--   The PStage construction uses the disjoint pool bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L340-L343
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L340-L343

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_bundle

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.PStage.disjoint_pool_bundle (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by sorry
