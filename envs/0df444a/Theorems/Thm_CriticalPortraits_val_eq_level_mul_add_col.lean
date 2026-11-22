-- Prove2me | Theorems.Thm_CriticalPortraits_val_eq_level_mul_add_col
-- name    : CriticalPortraits.val_eq_level_mul_add_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:38.213283+00:00
-- url     : https://prove2.me/theorems/a88725c9-dade-46a5-b1a0-e6533e77d5f6
-- title:
--   Critical Portraits: val eq level mul add col
-- statement:
--   Within one fiber, `val` is strictly monotone in level: a point's `.val` equals
--       `level * m + col`.  (Used to identify least-`.val` with lowest-level.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L286-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Portraits.lean#L286-L287

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

theorem CriticalPortraits.val_eq_level_mul_add_col {N : ℕ} (m : ℕ) (i : ZMod N) :
    i.val = (i.val / m) * m + i.val % m := by sorry
