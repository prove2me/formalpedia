-- Prove2me | Theorems.Thm_FltRegular_is_principal
-- name    : FltRegular.is_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:18.587939+00:00
-- url     : https://prove2.me/theorems/dde1fc9e-6d0f-4261-be21-67d6fc3268c0
-- title:
--   Flt Regular: is principal
-- statement:
--   The cyclotomic factor `a + ζ * b` is a unit times a `p`-th power.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L169-L175

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
local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K
variable [hpri : Fact p.Prime]

theorem FltRegular.is_principal {a b c : ℤ} {ζ : R} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c)
    (H : a ^ p + b ^ p = c ^ p) (hζ : IsPrimitiveRoot ζ p) :
    ∃ (u : Rˣ) (α : R), ↑u * α ^ p = ↑a + ζ * ↑b := by sorry
