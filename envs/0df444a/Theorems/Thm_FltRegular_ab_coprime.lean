-- Prove2me | Theorems.Thm_FltRegular_ab_coprime
-- name    : FltRegular.ab_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:23.328805+00:00
-- url     : https://prove2.me/theorems/e6e44e2c-379a-4075-b699-263b4338fc81
-- title:
--   Flt Regular: ab coprime
-- statement:
--   In a normalized Fermat solution, `a` and `b` are coprime.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L79-L94
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L79-L94

module
public import Mathlib.NumberTheory.FLT.Three
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
set_option autoImplicit false
@[expose] public section
public section
open Finset Nat IsCyclotomicExtension Ideal Polynomial Int Basis FltRegular.CaseI
open scoped NumberField
open FltRegular
variable {p : ℕ}

theorem FltRegular.ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) : IsCoprime a b := by sorry
