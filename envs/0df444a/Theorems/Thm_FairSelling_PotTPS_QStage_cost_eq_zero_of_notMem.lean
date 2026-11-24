-- Prove2me | Theorems.Thm_FairSelling_PotTPS_QStage_cost_eq_zero_of_notMem
-- name    : FairSelling.PotTPS.QStage.cost_eq_zero_of_notMem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:40.389049+00:00
-- url     : https://prove2.me/theorems/641c9657-7e39-499a-9a4d-ce75edcd7116
-- title:
--   QStage: cost eq zero of not Mem
-- statement:
--   The QStage construction uses the cost eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L355-L358
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPot.lean#L355-L358

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_ChargeTPS_cost_eq_zero_of_notMem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}

theorem FairSelling.PotTPS.QStage.cost_eq_zero_of_notMem {s : QStage G n} (hs : s.Good v p eps) {i : Fin n}
    (hi : i ∉ s.served) (j : Fin n) : s.cost v p i j = 0 := by sorry
