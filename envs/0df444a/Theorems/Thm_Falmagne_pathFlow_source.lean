-- Prove2me | Theorems.Thm_Falmagne_pathFlow_source
-- name    : Falmagne.pathFlow_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:46.925236+00:00
-- url     : https://prove2.me/theorems/29f10bc9-8eb2-579e-bb95-4fdebde58e82
-- title:
--   Falmagne: path Flow source
-- statement:
--   The Falmagne construction uses the path Flow source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L150-L154
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L150-L154

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem Falmagne.pathFlow_source (l : List X) (hl : l.Nodup) (hfull : l.toFinset = Finset.univ)
    [Nonempty X] : outflow (pathFlow l) Finset.univ = 1 := by sorry
