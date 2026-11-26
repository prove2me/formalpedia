-- Prove2me | Theorems.Thm_Falmagne_inflow_add
-- name    : Falmagne.inflow_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:28.793855+00:00
-- url     : https://prove2.me/theorems/bfd92633-5fff-5dc3-9d37-45e0b15133f0
-- title:
--   Falmagne: inflow add
-- statement:
--   The Falmagne construction uses the inflow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L37-L39
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L37-L39

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

theorem Falmagne.inflow_add (q r : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => q x B + r x B) A = inflow q A + inflow r A := by sorry
