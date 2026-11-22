-- Prove2me | Theorems.Thm_Egrs75_ConcreteMath_two_mul_padicValNat_three_centralBinom
-- name    : Egrs75.ConcreteMath.two_mul_padicValNat_three_centralBinom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:24:36.489036+00:00
-- url     : https://prove2.me/theorems/dd947f70-a9ac-4aa5-8da4-e8ff93c5e553
-- title:
--   Concrete Math: two mul padic Val Nat three central Binom
-- statement:
--   The ternary specialization of the central-binomial digit-excess formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L75-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/KummerValuation.lean#L75-L80

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

theorem Egrs75.ConcreteMath.two_mul_padicValNat_three_centralBinom (n : ℕ) :
    2 * padicValNat 3 (Nat.centralBinom n) =
      2 * (Nat.digits 3 n).sum - (Nat.digits 3 (2 * n)).sum := by sorry
