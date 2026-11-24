-- Prove2me | Theorems.Thm_FairSelling_losses_of_round
-- name    : FairSelling.losses_of_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:13.151531+00:00
-- url     : https://prove2.me/theorems/546d2ede-1b0b-458a-99c4-9bb698815d15
-- title:
--   Fair Selling: losses of round
-- statement:
--   **Proposition 5, one round of the main loop.**  If the state before the round is accounted
--   for and no available good is worth as much as its threshold to an active agent, and if the round
--   serves the agents of `Kset` with the parts `part` of a canonical partition `C` of agent `i`, then
--   the state after the round is accounted for.
--
--   Each served agent `b` accounts for the goods `C.goods (part b)` of its part and for the money
--   `C.cash (part b)` handed out with it; the good sold to fund the part (if any) is charged to the
--   first — in the order of `Fin n` — of the served agents whose part it funds, so that the events
--   are pairwise disjoint.
--
--   The classification of Definition 7 is then: an event with no sold good is of type `ℓ₂`, because
--   a still-active agent finds the part unacceptable (`hloss`); an event whose sold good `f` the
--   still-active agent intended to sell anyway is again of type `ℓ₂`; and otherwise the part is not
--   the special part, hence — by condition 2 of canonicity — is a singleton `{e}` funded entirely by
--   the sale of `f`, which is a loss of type `ℓ₃` (if `e` is not a good the agent intended to sell)
--   or `ℓ₄` (if it is).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L314-L462
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L314-L462

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.losses_of_round (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hInv : Inv v p T R D) {i : Fin n}
    (hmax : ∀ a ∈ T, MMS n (v a) p ≤ MMS n (v i) p)
    {k : ℕ} [NeZero k] (C : Canonical (v i) p (MMS n (v i) p) (thr v p i) k R D)
    (Kset : Finset (Fin n)) (part : Fin n → Fin k) (hKT : Kset ⊆ T)
    (hinj : Set.InjOn part Kset)
    (hloss : ∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
      vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < thr v p a)
    (hspecial : ∀ a ∈ Kset, a ≠ i → part a ≠ 0) (hzero : Kset = T ∨ part i ≠ 0) :
    Losses v p (T \ Kset)
      (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
      (D + (∑ g ∈ C.sold (Kset.image part), p g) - ∑ j ∈ Kset.image part, C.cash j) := by sorry
