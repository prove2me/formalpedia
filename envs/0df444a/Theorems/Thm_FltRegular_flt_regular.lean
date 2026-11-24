-- Prove2me | Theorems.Thm_FltRegular_flt_regular
-- name    : FltRegular.flt_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:45.497841+00:00
-- url     : https://prove2.me/theorems/6e9f887e-c5ce-459f-8b80-8136f427fdc8
-- title:
--   Flt Regular: flt regular
-- statement:
--   Fermat's last theorem for regular primes.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/FltRegular.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/FltRegular.lean#L21-L28

module
public import Mathlib.NumberTheory.FLT.Basic
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_CaseI_Statement
public import Definitions.Def_FltRegular_CaseII_Statement
public import Definitions.Def_FltRegular_FltRegular
set_option autoImplicit false
@[expose] public section
public section
open FltRegular

theorem FltRegular.flt_regular {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by sorry

alias «flt_regular» := FltRegular.flt_regular
