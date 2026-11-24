-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_own
-- name    : FairSelling.PotTPS.QStage.disjoint_pool_own
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:35.169925+00:00
-- url     : https://prove2.me/theorems/7a985195-2d2f-4364-9023-8e6618e34c03
-- title:
--   QStage: disjoint pool own
-- statement:
--   The QStage construction uses the disjoint pool own property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L226-L227
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L226-L227

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

theorem FairSelling.PotTPS.QStage.disjoint_pool_own (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.own i) := by sorry
