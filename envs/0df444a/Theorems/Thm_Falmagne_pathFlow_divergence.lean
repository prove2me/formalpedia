-- Prove2me | Theorems.Thm_Falmagne_pathFlow_divergence
-- name    : Falmagne.pathFlow_divergence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:21.830802+00:00
-- url     : https://prove2.me/theorems/fb538851-b943-467e-9358-08fe57026b22
-- title:
--   Falmagne: path Flow divergence
-- statement:
--   Divergence of the unit path of a duplicate-free list.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L134-L148
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L134-L148

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

theorem Falmagne.pathFlow_divergence (l : List X) (hl : l.Nodup) (A : Finset X) :
    outflow (pathFlow l) A - inflow (pathFlow l) A =
      (if A = l.toFinset then 1 else 0) - (if A = ∅ then 1 else 0) := by sorry
