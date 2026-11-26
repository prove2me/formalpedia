-- Prove2me | Theorems.Thm_Falmagne_lowerContour_subset_iff
-- name    : Falmagne.lowerContour_subset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:08.451468+00:00
-- url     : https://prove2.me/theorems/88638484-bd90-585e-8bb8-57f0d15c072c
-- title:
--   Falmagne: lower Contour subset iff
-- statement:
--   The Falmagne construction uses the lower Contour subset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L86-L92
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L86-L92

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

theorem Falmagne.lowerContour_subset_iff (hl : IsRanking l) :
    A ⊆ lowerContour l x ↔ ∀ y ∈ A, l.idxOf x ≤ l.idxOf y := by sorry
