-- Prove2me | Theorems.Thm_CriticalPortraits_val_le_iff_level_le_of_sameFiber
-- name    : CriticalPortraits.val_le_iff_level_le_of_sameFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:32.61256+00:00
-- url     : https://prove2.me/theorems/4e847934-0e3e-4f30-ae7d-d8294aa808a4
-- title:
--   Critical Portraits: val le iff level le of same Fiber
-- statement:
--   Within a single fiber (same residue mod `m`), the `.val` order equals the level order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L228-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L228-L238

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators

theorem CriticalPortraits.val_le_iff_level_le_of_sameFiber {N m : ℕ} {x y : ZMod N}
    (hxy : x.val % m = y.val % m) :
    x.val ≤ y.val ↔ x.val / m ≤ y.val / m := by sorry
