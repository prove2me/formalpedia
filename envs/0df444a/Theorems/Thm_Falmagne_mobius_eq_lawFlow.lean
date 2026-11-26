-- Prove2me | Theorems.Thm_Falmagne_mobius_eq_lawFlow
-- name    : Falmagne.mobius_eq_lawFlow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:04.236133+00:00
-- url     : https://prove2.me/theorems/173f4770-f824-4d53-8502-a847f2487dd0
-- title:
--   Falmagne: mobius eq law Flow
-- statement:
--   The Möbius coefficient equals the probability of the exact lower contour.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L46-L59
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L46-L59

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

theorem Falmagne.mobius_eq_lawFlow {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : ∀ l ∈ w.support, IsRanking l) (hp : Represents w p) (x : X) (A : Finset X)
    (hx : x ∈ A) :
    upperMobius (fun B => p B x) A = lawFlow w x A := by sorry
