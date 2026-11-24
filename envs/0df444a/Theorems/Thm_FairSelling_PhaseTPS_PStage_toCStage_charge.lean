-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_charge
-- name    : FairSelling.PhaseTPS.PStage.toCStage_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:38.706669+00:00
-- url     : https://prove2.me/theorems/a9100dec-9121-4066-8aef-333076a85abf
-- title:
--   PStage: to CStage charge
-- statement:
--   The PStage construction uses the to CStage charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L197-L199
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L197-L199

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]
open Classical

theorem FairSelling.PhaseTPS.PStage.toCStage_charge (s : PStage G n) (i : Fin n) :
    (s.toCStage).charge i = s.own i ∪ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k) := by sorry
