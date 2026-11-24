-- Prove2me | Theorems.Thm_FltRegular_is_principal_aux
-- name    : FltRegular.is_principal_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:25.307275+00:00
-- url     : https://prove2.me/theorems/a30e7612-358e-4898-8e5d-78125934965f
-- title:
--   Flt Regular: is principal aux
-- statement:
--   A `p`-th-power principal ideal has a generator that is a unit times a `p`-th power.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L132-L145

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

theorem FltRegular.is_principal_aux {K' : Type*} [Field K'] [CharZero K'] [IsCyclotomicExtension {p} ℚ K']
    [Fintype (ClassGroup (𝓞 K'))]
    {a b : ℤ} {ζ : 𝓞 K'} (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K'))
    {I : Ideal (𝓞 K')} (hI : span ({↑a + ζ * ↑b} : Set (𝓞 K')) = I ^ p) :
    ∃ (u : (𝓞 K')ˣ) (α : 𝓞 K'), ↑u * α ^ p = ↑a + ζ * ↑b := by sorry
