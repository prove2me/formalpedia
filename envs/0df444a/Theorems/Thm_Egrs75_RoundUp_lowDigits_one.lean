-- Prove2me | Theorems.Thm_Egrs75_RoundUp_lowDigits_one
-- name    : Egrs75.RoundUp.lowDigits_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:46.914801+00:00
-- url     : https://prove2.me/theorems/bb9a9d89-334b-4da0-82af-f404e77778a9
-- title:
--   Round Up: low Digits one
-- statement:
--   `LowDigits p 1` for `p ≥ 3` (digits of `1` are `[1]`, and `1 ≤ (p-1)/2`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L114-L117
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L114-L117

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

theorem Egrs75.RoundUp.lowDigits_one {p : ℕ} (hp : 3 ≤ p) : LowDigits p 1 := by sorry
