-- Prove2me | Theorems.Thm_Falmagne_inflow_sub
-- name    : Falmagne.inflow_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:26.701659+00:00
-- url     : https://prove2.me/theorems/9e22264e-a664-438f-aa70-b69dd52c80b2
-- title:
--   Falmagne: inflow sub
-- statement:
--   The Falmagne construction uses the inflow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L43-L45
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L43-L45

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

theorem Falmagne.inflow_sub (q r : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => q x B - r x B) A = inflow q A - inflow r A := by sorry
