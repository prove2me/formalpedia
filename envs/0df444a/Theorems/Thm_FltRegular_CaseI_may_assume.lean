-- Prove2me | Theorems.Thm_FltRegular_CaseI_may_assume
-- name    : FltRegular.CaseI.may_assume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:23.714338+00:00
-- url     : https://prove2.me/theorems/91bea143-f528-46a2-ab52-6a863c64c583
-- title:
--   Case I: may assume
-- statement:
--   It suffices to prove Case I under the additional normalized hypotheses.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L41-L74
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/CaseI/Statement.lean#L41-L74

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
open FltRegular.CaseI

theorem FltRegular.CaseI.may_assume : SlightlyEasier → Statement := by sorry
