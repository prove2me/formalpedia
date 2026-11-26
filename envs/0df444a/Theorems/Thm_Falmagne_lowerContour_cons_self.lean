-- Prove2me | Theorems.Thm_Falmagne_lowerContour_cons_self
-- name    : Falmagne.lowerContour_cons_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:19.486201+00:00
-- url     : https://prove2.me/theorems/187964b1-1730-59b1-bd79-43c94bd26606
-- title:
--   Falmagne: lower Contour cons self
-- statement:
--   The Falmagne construction uses the lower Contour cons self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L12-L15
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L12-L15

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_PathChoice
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {x y : X} {A : Finset X}

theorem Falmagne.lowerContour_cons_self (h : x ∉ l) :
    lowerContour (x :: l) x = (x :: l).toFinset := by sorry
