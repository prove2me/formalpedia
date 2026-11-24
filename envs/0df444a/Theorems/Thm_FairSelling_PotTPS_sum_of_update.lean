-- Prove2me | Theorems.Thm_FairSelling_PotTPS_sum_of_update
-- name    : FairSelling.PotTPS.sum_of_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:16.345799+00:00
-- url     : https://prove2.me/theorems/ee42eaf9-5796-4db6-90de-37a93088eecd
-- title:
--   Pot TPS: sum of update
-- statement:
--   The Pot TPS construction uses the sum of update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L43-L50
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L43-L50

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.PotTPS.sum_of_update {N : ℕ} (F F' : Fin N → ℝ) (k : Fin N) (h : ∀ i, i ≠ k → F' i = F i) :
    ∑ i, F' i = ∑ i, F i - F k + F' k := by sorry
