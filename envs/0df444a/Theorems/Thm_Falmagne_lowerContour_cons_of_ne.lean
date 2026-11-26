-- Prove2me | Theorems.Thm_Falmagne_lowerContour_cons_of_ne
-- name    : Falmagne.lowerContour_cons_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:22.003228+00:00
-- url     : https://prove2.me/theorems/9c372b9a-302a-48a6-aea6-c08ccc4f3d49
-- title:
--   Falmagne: lower Contour cons of ne
-- statement:
--   The Falmagne construction uses the lower Contour cons of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L17-L23
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L17-L23

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

theorem Falmagne.lowerContour_cons_of_ne (hxy : x ≠ y) (hyn : y ∉ l) :
    lowerContour (y :: l) x = lowerContour l x := by sorry
