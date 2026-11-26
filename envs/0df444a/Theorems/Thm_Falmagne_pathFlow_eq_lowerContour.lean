-- Prove2me | Theorems.Thm_Falmagne_pathFlow_eq_lowerContour
-- name    : Falmagne.pathFlow_eq_lowerContour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:16.590246+00:00
-- url     : https://prove2.me/theorems/2e53ffd3-868e-54e3-9468-68ce8913eb1c
-- title:
--   Falmagne: path Flow eq lower Contour
-- statement:
--   The Falmagne construction uses the path Flow eq lower Contour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L25-L38
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean#L25-L38

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

theorem Falmagne.pathFlow_eq_lowerContour (hl : l.Nodup) (hx : x ∈ l) :
    pathFlow l x A = if A = lowerContour l x then 1 else 0 := by sorry
