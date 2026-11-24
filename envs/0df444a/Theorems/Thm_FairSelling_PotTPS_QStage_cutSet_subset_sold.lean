-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_cutSet_subset_sold
-- name    : FairSelling.PotTPS.QStage.cutSet_subset_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:18.706034+00:00
-- url     : https://prove2.me/theorems/09b56c40-8038-4d6e-845b-764ad7134dbf
-- title:
--   QStage: cut Set subset sold
-- statement:
--   The QStage construction uses the cut Set subset sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L209-L210
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L209-L210

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

theorem FairSelling.PotTPS.QStage.cutSet_subset_sold (s : QStage G n) : s.cutSet ⊆ s.sold := by sorry
