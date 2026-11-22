-- Prove2me | Theorems.Thm_Egrs75_RoundUp_lowDigits_ru
-- name    : Egrs75.RoundUp.lowDigits_ru
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.166441+00:00
-- url     : https://prove2.me/theorems/e4eae558-0e7c-44ab-8f7d-03a7bf765510
-- title:
--   Round Up: low Digits ru
-- statement:
--   `ru p x` has all base-`p` digits `≤ (p-1)/2`. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L120-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L120-L142

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

theorem Egrs75.RoundUp.lowDigits_ru {p : ℕ} (hp : 3 ≤ p) (x : ℕ) : LowDigits p (ru p x) := by sorry
