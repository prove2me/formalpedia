-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_mem_cutSet
-- name    : FairSelling.PotTPS.QStage.mem_cutSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:28:02.491937+00:00
-- url     : https://prove2.me/theorems/9d3b86e5-b76a-4c1c-a9dc-544fb09e281b
-- title:
--   QStage: mem cut Set
-- statement:
--   The QStage construction uses the mem cut Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L197-L198
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L197-L198

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

theorem FairSelling.PotTPS.QStage.mem_cutSet {s : QStage G n} {g : G} {i : Fin n} (h : g ∈ s.src i) : g ∈ s.cutSet := by sorry
