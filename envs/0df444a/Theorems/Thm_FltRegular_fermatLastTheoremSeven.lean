-- Prove2me | Theorems.Thm_FltRegular_fermatLastTheoremSeven
-- name    : FltRegular.fermatLastTheoremSeven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:52.585149+00:00
-- url     : https://prove2.me/theorems/86ce8f85-3c0b-4cd3-8dec-d8953af70aad
-- title:
--   Flt Regular: fermat Last Theorem Seven
-- statement:
--   Fermat's Last Theorem for exponent seven.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/FLT7.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/FLT7.lean#L26-L27

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension

theorem FltRegular.fermatLastTheoremSeven : FermatLastTheoremFor 7 := by sorry

alias «fermatLastTheoremSeven» := FltRegular.fermatLastTheoremSeven
