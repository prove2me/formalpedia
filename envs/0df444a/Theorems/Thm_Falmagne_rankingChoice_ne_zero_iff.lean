-- Prove2me | Theorems.Thm_Falmagne_rankingChoice_ne_zero_iff
-- name    : Falmagne.rankingChoice_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:13:29.583378+00:00
-- url     : https://prove2.me/theorems/33ce3cb1-3bd1-4f4f-8a5c-ed052996758a
-- title:
--   Falmagne: ranking Choice ne zero iff
-- statement:
--   The Falmagne construction uses the ranking Choice ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L82-L84
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Basic.lean#L82-L84

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

theorem Falmagne.rankingChoice_ne_zero_iff :
    rankingChoice l A x ≠ 0 ↔ x ∈ A ∧ A ⊆ lowerContour l x := by sorry
