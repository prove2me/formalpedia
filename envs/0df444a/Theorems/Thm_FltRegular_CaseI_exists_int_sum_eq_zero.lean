-- Prove2me | Theorems.Thm_FltRegular_CaseI_exists_int_sum_eq_zero
-- name    : FltRegular.CaseI.exists_int_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:55.911641+00:00
-- url     : https://prove2.me/theorems/35fc628c-8ebe-4da7-890d-f87fcf76a930
-- title:
--   Case I: exists int sum eq zero
-- statement:
--   An integer exponent giving the Case I complex-conjugation congruence modulo `p`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/CaseI.lean#L81-L94

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

theorem FltRegular.CaseI.exists_int_sum_eq_zero (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      (zetaUnit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by sorry
