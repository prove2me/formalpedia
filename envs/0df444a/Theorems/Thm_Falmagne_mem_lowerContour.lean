-- Prove2me | Theorems.Thm_Falmagne_mem_lowerContour
-- name    : Falmagne.mem_lowerContour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:00.837164+00:00
-- url     : https://prove2.me/theorems/27705d4c-2773-57b6-9f4a-943afd70fde4
-- title:
--   Falmagne: mem lower Contour
-- statement:
--   The Falmagne construction uses the mem lower Contour property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L62-L64
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L62-L64

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}

theorem Falmagne.mem_lowerContour (l : List X) (x y : X) :
    y ∈ lowerContour l x ↔ y ∈ l ∧ l.idxOf x ≤ l.idxOf y := by sorry
