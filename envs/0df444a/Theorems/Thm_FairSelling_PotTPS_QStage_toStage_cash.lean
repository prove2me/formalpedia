-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
-- name    : FairSelling.PotTPS.QStage.toStage_cash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:59.170403+00:00
-- url     : https://prove2.me/theorems/f02f0789-86e7-4a2c-a301-f3f63c21d6b9
-- title:
--   QStage: to Stage cash
-- statement:
--   The QStage construction uses the to Stage cash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L473-L473
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L473-L473

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash


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

theorem FairSelling.PotTPS.QStage.toStage_cash (s : QStage G n) : (s.toStage).cash = s.cash := by sorry

attribute [defeq] FairSelling.PotTPS.QStage.toStage_cash
