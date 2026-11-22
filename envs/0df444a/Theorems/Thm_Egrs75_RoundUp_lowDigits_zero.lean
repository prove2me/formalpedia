-- Prove2me | Theorems.Thm_Egrs75_RoundUp_lowDigits_zero
-- name    : Egrs75.RoundUp.lowDigits_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:36.529941+00:00
-- url     : https://prove2.me/theorems/d28357f0-7d84-4cce-b273-0ee9b46199f1
-- title:
--   Round Up: low Digits zero
-- statement:
--   `0` has no digits, hence `LowDigits p 0` vacuously.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L86-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L86-L88

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)

theorem Egrs75.RoundUp.lowDigits_zero (p : ℕ) : LowDigits p 0 := by sorry
