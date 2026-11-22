-- Prove2me | Theorems.Thm_AbstractLaminar_roots_width_sum_le
-- name    : AbstractLaminar.roots_width_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:18.299565+00:00
-- url     : https://prove2.me/theorems/a08b1d78-6af3-48b0-90d5-2e1b7d6d6866
-- title:
--   Abstract Laminar: roots width sum le
-- statement:
--   Sum of root widths is at most the window width.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L348-L362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L348-L362

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

theorem AbstractLaminar.roots_width_sum_le :
    ∑ r ∈ Roots fam a b, (fam.hi r - fam.lo r) ≤ b - a := by sorry
