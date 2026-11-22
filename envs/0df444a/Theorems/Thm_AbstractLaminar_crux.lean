-- Prove2me | Theorems.Thm_AbstractLaminar_crux
-- name    : AbstractLaminar.crux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:03.235418+00:00
-- url     : https://prove2.me/theorems/574fab01-7da3-464c-82c4-bb0e87c3b363
-- title:
--   Abstract Laminar: crux
-- statement:
--   THE CRUX: if the window has a top edge, the root subtree widths do not cover it.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L365-L433
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L365-L433

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}

theorem AbstractLaminar.crux (hab : a < b) (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a - 1 := by sorry
