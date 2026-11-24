-- Prove2me | Theorems.Thm_FltRegular_caseI_easier
-- name    : FltRegular.caseI_easier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:31.688967+00:00
-- url     : https://prove2.me/theorems/87da3658-1130-4989-bb39-2482e28718da
-- title:
--   Flt Regular: case I easier
-- statement:
--   Case I with additional assumptions.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L228-L261
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L228-L261

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

theorem FltRegular.caseI_easier {a b c : ℤ} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hab : ¬a ≡ b [ZMOD p])
    (caseI : ¬↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by sorry
