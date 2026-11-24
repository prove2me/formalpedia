-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
-- name    : FairSelling.PotTPS.QStage.toStage_soldSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:22:39.490234+00:00
-- url     : https://prove2.me/theorems/64d79c28-d26c-42b0-ae70-79e742b61aa4
-- title:
--   QStage: to Stage sold Set
-- statement:
--   The QStage construction uses the to Stage sold Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L475-L475
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L475-L475

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
variable {v p eps}
omit [Fintype G]

theorem FairSelling.PotTPS.QStage.toStage_soldSet (s : QStage G n) : (s.toStage).soldSet = s.sold := by sorry

attribute [defeq] FairSelling.PotTPS.QStage.toStage_soldSet
