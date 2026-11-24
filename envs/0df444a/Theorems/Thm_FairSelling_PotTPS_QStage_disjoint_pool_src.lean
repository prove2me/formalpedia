-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_src
-- name    : FairSelling.PotTPS.QStage.disjoint_pool_src
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:36.554589+00:00
-- url     : https://prove2.me/theorems/51e59315-b93c-4510-a6ef-496ea9d9bb8c
-- title:
--   QStage: disjoint pool src
-- statement:
--   The QStage construction uses the disjoint pool src property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L229-L230
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L229-L230

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PotTPS.QStage.disjoint_pool_src (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.src i) := by sorry
