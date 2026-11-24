-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
-- name    : FairSelling.PotTPS.QStage.toStage_bundle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:48.096066+00:00
-- url     : https://prove2.me/theorems/61de592a-adaf-4a7b-a532-c4cc54498261
-- title:
--   QStage: to Stage bundle
-- statement:
--   The QStage construction uses the to Stage bundle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L471-L471
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L471-L471

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
omit [Fintype G]

theorem FairSelling.PotTPS.QStage.toStage_bundle (s : QStage G n) : (s.toStage).bundle = s.bundle := by sorry

attribute [defeq] FairSelling.PotTPS.QStage.toStage_bundle
