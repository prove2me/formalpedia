-- Prove2me | Theorems.Thm_BooleanFun_BV_zero_not_unanimous
-- name    : BooleanFun.BV.zero_not_unanimous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:07:16.033413+00:00
-- url     : https://prove2.me/theorems/824a0b00-4ea7-4fa7-806e-d2e1f2150497
-- title:
--   BV: zero not unanimous
-- statement:
--   The (unique) voting rule for zero voters is not unanimous.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L109-L116
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L109-L116

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV.zero_not_unanimous (f : BooleanFunc n) (hn : n = 0) : ¬IsUnanimous f := by sorry
