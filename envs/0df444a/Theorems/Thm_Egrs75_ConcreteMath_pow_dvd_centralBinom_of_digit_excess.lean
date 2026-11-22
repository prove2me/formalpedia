-- Prove2me | Theorems.Thm_Egrs75_ConcreteMath_pow_dvd_centralBinom_of_digit_excess
-- name    : Egrs75.ConcreteMath.pow_dvd_centralBinom_of_digit_excess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:31.167303+00:00
-- url     : https://prove2.me/theorems/ccf44d34-90f8-4959-b498-ed30121e20a1
-- title:
--   Concrete Math: pow dvd central Binom of digit excess
-- statement:
--   **`p^m` divides `Nat.centralBinom n` from a Kummer digit bound.**
--
--   If `2 * S_p(n) - S_p(2n) ≥ (p - 1) * m`, then `p^m ∣ C(2n,n)`.
--   This is the reusable bridge from digit/carry certificates to
--   central-binomial divisibility.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L59-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L59-L72

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_LeanPool_Egrs75_KummerValuation
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ConcreteMath
open Nat

theorem Egrs75.ConcreteMath.pow_dvd_centralBinom_of_digit_excess
    {p n m : ℕ} [hp : Fact p.Prime]
    (h : (p - 1) * m ≤
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum) :
    p ^ m ∣ Nat.centralBinom n := by sorry
