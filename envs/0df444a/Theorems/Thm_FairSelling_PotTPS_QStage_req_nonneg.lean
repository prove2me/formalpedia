-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_req_nonneg
-- name    : FairSelling.PotTPS.QStage.req_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:48:17.989723+00:00
-- url     : https://prove2.me/theorems/c2bec205-7473-4cc3-8267-75b1fb47e87d
-- title:
--   QStage: req nonneg
-- statement:
--   The QStage construction uses the req nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L247-L257
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L247-L257

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.req_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j := by sorry
