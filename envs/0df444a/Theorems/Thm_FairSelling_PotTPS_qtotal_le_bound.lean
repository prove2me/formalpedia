-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qtotal_le_bound
-- name    : FairSelling.PotTPS.qtotal_le_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:47.836472+00:00
-- url     : https://prove2.me/theorems/8d99b956-2636-4bef-b8b7-a4bcaf4a56e1
-- title:
--   Pot TPS: qtotal le bound
-- statement:
--   The Pot TPS construction uses the qtotal le bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L556-L558
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L556-L558

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
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PotTPS.qtotal_le_bound (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p := by sorry
