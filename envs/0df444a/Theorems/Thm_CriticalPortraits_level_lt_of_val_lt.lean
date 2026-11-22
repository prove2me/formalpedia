-- Prove2me | Theorems.Thm_CriticalPortraits_level_lt_of_val_lt
-- name    : CriticalPortraits.level_lt_of_val_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:44.773846+00:00
-- url     : https://prove2.me/theorems/0cb19071-0e8f-47f5-bdc7-56f85cb5a4e1
-- title:
--   Critical Portraits: level lt of val lt
-- statement:
--   Same-fiber `.val` comparison is the level comparison (strict).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L661-L665
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L661-L665

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

theorem CriticalPortraits.level_lt_of_val_lt [NeZero (d * m)] {x y : ZMod (d * m)}
    (hfib : x.val % m = y.val % m) (h : x.val < y.val) : x.val / m < y.val / m := by sorry
