-- Prove2me | Theorems.Thm_FairSelling_losses_budget
-- name    : FairSelling.losses_budget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:12:28.705915+00:00
-- url     : https://prove2.me/theorems/f7dfdd9b-451f-48a1-8dfb-c553089adbd7
-- title:
--   Fair Selling: losses budget
-- statement:
--   **The value still at the disposal of an active agent.**  In any state satisfying the
--   accounting invariant, every active agent `i` has an equi-valued MMS partition whose budget in that
--   state is at least `|T| · MMSᵢ`, where `T` is the set of still-active agents.
--
--   This is the manuscript's "the total value that we have at our disposal is at least `n′ · MMSᵢ`",
--   and it is the interface between the loss accounting (Proposition 5) and Lemma 9.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L420-L461
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsBudget.lean#L420-L461

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.losses_budget (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (hL : Losses v p T R D) {i : Fin n} (hi : i ∈ T) :
    ∃ E : EquiMMS (v i) p (MMS n (v i) p) n,
      ((T.card : ℝ)) * MMS n (v i) p ≤ E.budget R D := by sorry
