-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_cutSet
-- name    : FairSelling.PotTPS.QStage.disjoint_pool_cutSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:55.361839+00:00
-- url     : https://prove2.me/theorems/cb85b639-f81d-4c56-a5ae-bd4658f06f9e
-- title:
--   QStage: disjoint pool cut Set
-- statement:
--   The QStage construction uses the disjoint pool cut Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L232-L233
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L232-L233

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

theorem FairSelling.PotTPS.QStage.disjoint_pool_cutSet (s : QStage G n) : Disjoint s.pool s.cutSet := by sorry
