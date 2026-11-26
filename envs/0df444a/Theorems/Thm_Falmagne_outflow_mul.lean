-- Prove2me | Theorems.Thm_Falmagne_outflow_mul
-- name    : Falmagne.outflow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:42.622573+00:00
-- url     : https://prove2.me/theorems/a38e53b0-7802-45c4-8f17-718d1fa89670
-- title:
--   Falmagne: outflow mul
-- statement:
--   The Falmagne construction uses the outflow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L46-L48
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L46-L48

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

theorem Falmagne.outflow_mul (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => a * q x B) A = a * outflow q A := by sorry
