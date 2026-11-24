-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qtotal_nonneg
-- name    : FairSelling.PotTPS.qtotal_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:47.513078+00:00
-- url     : https://prove2.me/theorems/0339e66f-d9e9-4a9a-b5e2-9724928976b8
-- title:
--   Pot TPS: qtotal nonneg
-- statement:
--   The Pot TPS construction uses the qtotal nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L560-L562
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L560-L562

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

theorem FairSelling.PotTPS.qtotal_nonneg (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p := by sorry
