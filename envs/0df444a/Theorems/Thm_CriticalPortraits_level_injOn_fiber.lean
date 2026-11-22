-- Prove2me | Theorems.Thm_CriticalPortraits_level_injOn_fiber
-- name    : CriticalPortraits.level_injOn_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:33.913175+00:00
-- url     : https://prove2.me/theorems/8547b09a-0616-4e15-9c89-f0ed2aca6251
-- title:
--   Critical Portraits: level inj On fiber
-- statement:
--   The level is injective on a single fiber: same fiber + same level ⇒ same `.val` ⇒
--       same element.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L242-L247
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L242-L247

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

theorem CriticalPortraits.level_injOn_fiber {N m : ℕ} [NeZero N] {x y : ZMod N}
    (hxy : x.val % m = y.val % m) (hlev : x.val / m = y.val / m) : x = y := by sorry
