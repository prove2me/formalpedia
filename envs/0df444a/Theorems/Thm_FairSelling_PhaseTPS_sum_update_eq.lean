-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_sum_update_eq
-- name    : FairSelling.PhaseTPS.sum_update_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:33.225462+00:00
-- url     : https://prove2.me/theorems/14d51487-ef64-42f9-b017-69c5f79effb8
-- title:
--   Phase TPS: sum update eq
-- statement:
--   The Phase TPS construction uses the sum update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseStep.lean#L44-L51
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseStep.lean#L44-L51

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.PhaseTPS.sum_update_eq {n : ℕ} (f : Fin n → ℝ) (k : Fin n) (a : ℝ) :
    ∑ i, Function.update f k a i = ∑ i, f i - f k + a := by sorry
