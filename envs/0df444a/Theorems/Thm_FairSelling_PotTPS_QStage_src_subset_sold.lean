-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_src_subset_sold
-- name    : FairSelling.PotTPS.QStage.src_subset_sold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:29.297367+00:00
-- url     : https://prove2.me/theorems/a0fc81a4-a4da-4100-96f3-0974e318dab9
-- title:
--   QStage: src subset sold
-- statement:
--   The QStage construction uses the src subset sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L213-L214
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L213-L214

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

theorem FairSelling.PotTPS.QStage.src_subset_sold (s : QStage G n) (i : Fin n) : s.src i ⊆ s.sold := by sorry
