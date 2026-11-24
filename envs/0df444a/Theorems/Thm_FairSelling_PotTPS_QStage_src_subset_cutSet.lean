-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_src_subset_cutSet
-- name    : FairSelling.PotTPS.QStage.src_subset_cutSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:47:36.783808+00:00
-- url     : https://prove2.me/theorems/8daf0f1d-a77e-4ac2-a907-4490b9b69ee2
-- title:
--   QStage: src subset cut Set
-- statement:
--   The QStage construction uses the src subset cut Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L201-L202
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L201-L202

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

theorem FairSelling.PotTPS.QStage.src_subset_cutSet (s : QStage G n) (i : Fin n) : s.src i ⊆ s.cutSet := by sorry
