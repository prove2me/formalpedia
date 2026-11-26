-- Prove2me | Theorems.Thm_Falmagne_inflow_mul
-- name    : Falmagne.inflow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:40.800652+00:00
-- url     : https://prove2.me/theorems/29c34ad8-2e5e-54e8-a9fa-5f8eff5e7890
-- title:
--   Falmagne: inflow mul
-- statement:
--   The Falmagne construction uses the inflow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L49-L52
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L49-L52

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

theorem Falmagne.inflow_mul (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => a * q x B) A = a * inflow q A := by sorry
