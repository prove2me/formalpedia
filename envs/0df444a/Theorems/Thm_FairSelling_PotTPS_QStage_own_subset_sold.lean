-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_own_subset_sold
-- name    : FairSelling.PotTPS.QStage.own_subset_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:23.201546+00:00
-- url     : https://prove2.me/theorems/51ec482e-c606-40c8-b664-37772b795813
-- title:
--   QStage: own subset sold
-- statement:
--   The QStage construction uses the own subset sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L205-L206
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L205-L206

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
omit [Fintype G]

theorem FairSelling.PotTPS.QStage.own_subset_sold (s : QStage G n) (i : Fin n) : s.own i ⊆ s.sold := by sorry
