-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_toStage_pool
-- name    : FairSelling.PotTPS.QStage.toStage_pool
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:51:21.453631+00:00
-- url     : https://prove2.me/theorems/9cb09f1f-8d60-4ce1-9508-8ca0a5c5e90c
-- title:
--   QStage: to Stage pool
-- statement:
--   The QStage construction uses the to Stage pool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L477-L477
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L477-L477

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_pool

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.toStage_pool (s : QStage G n) : (s.toStage).pool = s.pool := by sorry
