-- Prove2me | Theorems.Thm_Falmagne_chosen_unique
-- name    : Falmagne.chosen_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:10.685794+00:00
-- url     : https://prove2.me/theorems/4e85596c-04d7-41ec-87c0-d9edbbce0163
-- title:
--   Falmagne: chosen unique
-- statement:
--   The Falmagne construction uses the chosen unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L94-L99
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L94-L99

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

theorem Falmagne.chosen_unique (hl : IsRanking l)
    (hx : x ∈ A ∧ A ⊆ lowerContour l x)
    (hy : y ∈ A ∧ A ⊆ lowerContour l y) : x = y := by sorry
