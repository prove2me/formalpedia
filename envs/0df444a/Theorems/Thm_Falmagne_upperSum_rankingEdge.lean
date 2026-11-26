-- Prove2me | Theorems.Thm_Falmagne_upperSum_rankingEdge
-- name    : Falmagne.upperSum_rankingEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:51.164874+00:00
-- url     : https://prove2.me/theorems/f06286e4-be0f-56ba-affb-e8bbe5945071
-- title:
--   Falmagne: upper Sum ranking Edge
-- statement:
--   The Falmagne construction uses the upper Sum ranking Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L13-L32
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L13-L32

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

theorem Falmagne.upperSum_rankingEdge (hl : IsRanking l) (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (rankingEdge l x) A = rankingChoice l A x := by sorry
