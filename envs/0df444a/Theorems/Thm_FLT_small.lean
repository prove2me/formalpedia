-- Prove2me | Theorems.Thm_FLT_small
-- name    : FLT_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:17:08.424233+00:00
-- url     : https://prove2.me/theorems/30a4e9bb-5b14-45d7-a801-bb6c09bddd1d
-- title:
--   FLT small: FLT small
-- statement:
--   Fermat's Last Theorem holds for every exponent in the interval `[3, 10]`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/SmallNumbers.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/SmallNumbers.lean#L21-L30

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
public import Definitions.Def_FltRegular_SmallNumbers_SmallNumbers
set_option autoImplicit false
@[expose] public section
public section

theorem FLT_small {n : ℕ} (hn : n ∈ Finset.Icc 3 10) : FermatLastTheoremFor n := by sorry
