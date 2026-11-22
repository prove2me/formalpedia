-- Prove2me | Theorems.Thm_AbstractLaminar_roots_width_sum_eq
-- name    : AbstractLaminar.roots_width_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:59.252677+00:00
-- url     : https://prove2.me/theorems/eb12ace3-2b01-40cf-a35a-01269117fbaa
-- title:
--   Abstract Laminar: roots width sum eq
-- statement:
--   Saturated window with a top edge: the root subtree widths sum to exactly `b - a - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L144-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L144-L159

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)

theorem AbstractLaminar.roots_width_sum_eq {a b : ℕ} (hab : a < b) (hsat : N fam a b = b - a)
    (htop : (topEdges fam a b).Nonempty) :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) = b - a - 1 := by sorry
