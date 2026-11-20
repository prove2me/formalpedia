-- Prove2me | Theorems.Thm_BooleanFun_BV_walsh_boolean_valued
-- name    : BooleanFun.BV.walsh_boolean_valued
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:23.970168+00:00
-- url     : https://prove2.me/theorems/7217f0f1-1acc-4490-989c-dcb07a36d1bb
-- title:
--   BV: walsh boolean valued
-- statement:
--   Walsh characters are Boolean valued.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L65-L66
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L65-L66

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.walsh_boolean_valued (S : Finset (Fin n)) : BooleanValued (χ S) := by sorry
