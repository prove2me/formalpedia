-- Prove2me | Theorems.Thm_Falmagne_outflow_add
-- name    : Falmagne.outflow_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:23:23.543386+00:00
-- url     : https://prove2.me/theorems/b5268518-b079-535a-aebe-f6c63f07ea6e
-- title:
--   Falmagne: outflow add
-- statement:
--   The Falmagne construction uses the outflow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L34-L36
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Path.lean#L34-L36

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

theorem Falmagne.outflow_add (q r : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => q x B + r x B) A = outflow q A + outflow r A := by sorry
