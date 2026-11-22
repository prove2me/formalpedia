-- Prove2me | Theorems.Thm_Egrs75_RoundUp_one_le_half
-- name    : Egrs75.RoundUp.one_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:49.044687+00:00
-- url     : https://prove2.me/theorems/3a742865-46e4-47c3-8304-e21381870969
-- title:
--   Round Up: one le half
-- statement:
--   For `p ≥ 3`, the digit `1 ≤ (p-1)/2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L108-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L108-L111

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

theorem Egrs75.RoundUp.one_le_half {p : ℕ} (hp : 3 ≤ p) : (1 : ℕ) ≤ (p - 1) / 2 := by sorry
