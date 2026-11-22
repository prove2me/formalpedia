-- Prove2me | Theorems.Thm_Egrs75_RoundUp_lowDigits_cons
-- name    : Egrs75.RoundUp.lowDigits_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:44.736168+00:00
-- url     : https://prove2.me/theorems/c4541243-3af2-4150-a3d1-e90b8791c8f2
-- title:
--   Round Up: low Digits cons
-- statement:
--   A low last digit on top of a low number stays low: `LowDigits p (p*m + d)`
--   when `d ≤ (p-1)/2` and `LowDigits p m` (and `2 ≤ p`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L92-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L92-L105

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

theorem Egrs75.RoundUp.lowDigits_cons {p m d : ℕ} (hp : 2 ≤ p) (hd : d ≤ (p - 1) / 2)
    (hm : LowDigits p m) : LowDigits p (p * m + d) := by sorry
