-- Prove2me | Theorems.Thm_FairSelling_PotTPS_pot_of_update
-- name    : FairSelling.PotTPS.pot_of_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:36.31079+00:00
-- url     : https://prove2.me/theorems/2743ea49-aa7b-43df-98ba-4c9821ed10eb
-- title:
--   Pot TPS: pot of update
-- statement:
--   How the pot of a good changes when a single agent's slice is replaced.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L54-L78
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L54-L78

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.PotTPS.pot_of_update {s t : QStage G n} {k : Fin n} {Src : Finset G} {q : ℝ} (p : G → ℝ)
    (hsrc : t.src = Function.update s.src k Src) (hcash : t.cash = Function.update s.cash k q)
    (g : G) :
    t.pot p g = s.pot p g + (if g ∈ s.src k then s.cash k else 0)
      - (if g ∈ Src then q else 0) := by sorry
