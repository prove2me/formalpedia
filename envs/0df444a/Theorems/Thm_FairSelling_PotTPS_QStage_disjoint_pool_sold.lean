-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_sold
-- name    : FairSelling.PotTPS.QStage.disjoint_pool_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:54.702391+00:00
-- url     : https://prove2.me/theorems/f75e98f1-96d9-4721-8b85-317385e75093
-- title:
--   QStage: disjoint pool sold
-- statement:
--   The QStage construction uses the disjoint pool sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L216-L219
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L216-L219

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

theorem FairSelling.PotTPS.QStage.disjoint_pool_sold (s : QStage G n) : Disjoint s.pool s.sold := by sorry
