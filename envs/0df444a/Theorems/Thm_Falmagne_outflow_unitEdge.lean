-- Prove2me | Theorems.Thm_Falmagne_outflow_unitEdge
-- name    : Falmagne.outflow_unitEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:23.185691+00:00
-- url     : https://prove2.me/theorems/206a3196-7515-5fb4-a160-f48ecdce46d1
-- title:
--   Falmagne: outflow unit Edge
-- statement:
--   The Falmagne construction uses the outflow unit Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L54-L60
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L54-L60

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

theorem Falmagne.outflow_unitEdge (hy : y ∈ B) (A : Finset X) :
    outflow (unitEdge y B) A = if A = B then 1 else 0 := by sorry
