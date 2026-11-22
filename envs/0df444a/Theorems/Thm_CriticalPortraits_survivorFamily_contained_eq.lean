-- Prove2me | Theorems.Thm_CriticalPortraits_survivorFamily_contained_eq
-- name    : CriticalPortraits.survivorFamily_contained_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:00.148832+00:00
-- url     : https://prove2.me/theorems/b20be8e5-0949-47a5-90d6-2f1195d1e899
-- title:
--   Critical Portraits: survivor Family contained eq
-- statement:
--   The window `(0, d-1]` contains every edge of the survivor family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L482-L492
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L482-L492

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
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.survivorFamily_contained_eq [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.contained (survivorFamily hd hm hP) 0 (d - 1) = T P := by sorry
