-- Prove2me | Theorems.Thm_Egrs75_RoundUp_exists_lowDigits_between
-- name    : Egrs75.RoundUp.exists_lowDigits_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:40.645337+00:00
-- url     : https://prove2.me/theorems/2acd403d-1f64-44b7-93bc-25f0caa876d7
-- title:
--   Round Up: exists low Digits between
-- statement:
--   **EGRS density Fact (existence form).** For an odd prime base `p ≥ 3` (in fact
--   any odd `p ≥ 3`) and every `x ≥ 1`, the interval `[x, 2x)` contains a `LowDigits p`
--   number. This is the single load-bearing density input from EGRS75's proof of
--   their Theorem 1. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L236-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L236-L239

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

theorem Egrs75.RoundUp.exists_lowDigits_between {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (x : ℕ)
    (hx : 1 ≤ x) : ∃ m, x ≤ m ∧ m < 2 * x ∧ LowDigits p m := by sorry
