-- Prove2me | Theorems.Thm_CriticalPortraits_minVal_lt_survivor
-- name    : CriticalPortraits.minVal_lt_survivor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:38.572182+00:00
-- url     : https://prove2.me/theorems/31148e30-e3e8-4679-8462-bcba580de547
-- title:
--   Critical Portraits: min Val lt survivor
-- statement:
--   The dropped point (the minimum) is strictly below — in LEVEL — every survivor of that set.
--       This is what makes "survivors = edge tops" hold; each critical set keeps exactly its tops.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L262-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L262-L278

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

theorem CriticalPortraits.minVal_lt_survivor {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {S : Finset (ZMod (d * m))} (hS : IsCriticalSet d m S) (h : S.Nonempty) :
    ∀ x ∈ eraseMin S, (minVal S h).val / m < x.val / m := by sorry
