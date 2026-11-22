-- Prove2me | Theorems.Thm_Egrs75_ConcreteMath_sub_one_mul_padicValNat_centralBinom
-- name    : Egrs75.ConcreteMath.sub_one_mul_padicValNat_centralBinom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:33.589816+00:00
-- url     : https://prove2.me/theorems/93eb0b61-5400-43c5-892d-ccd295cb1fbc
-- title:
--   Concrete Math: sub one mul padic Val Nat central Binom
-- statement:
--   **General `p`-adic formula for central binomial coefficients.**
--
--   For any prime `p`,
--   `(p - 1) * ν_p(C(2n,n)) = 2 * S_p(n) - S_p(2n)`, where `S_p`
--   is the sum of base-`p` digits. This is Kummer's theorem specialized to
--   `Nat.centralBinom`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L38-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L38-L52

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

theorem Egrs75.ConcreteMath.sub_one_mul_padicValNat_centralBinom (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) =
      2 * (Nat.digits p n).sum - (Nat.digits p (2 * n)).sum := by sorry
