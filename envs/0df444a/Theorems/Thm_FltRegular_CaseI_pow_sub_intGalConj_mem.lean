-- Prove2me | Theorems.Thm_FltRegular_CaseI_pow_sub_intGalConj_mem
-- name    : FltRegular.CaseI.pow_sub_intGalConj_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:44.816504+00:00
-- url     : https://prove2.me/theorems/b0a27992-3408-4cb7-b807-e6676ee38486
-- title:
--   Case I: pow sub int Gal Conj mem
-- statement:
--   The difference between a `p`-th power and its complex conjugate is divisible by `p`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L33-L42

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
open FractionalIdeal NumberField IsCMField
open FltRegular FltRegular.CaseI
omit [NeZero p]

theorem FltRegular.CaseI.pow_sub_intGalConj_mem (α : 𝓞 K) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by sorry
