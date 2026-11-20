-- Prove2me | Theorems.Thm_BooleanFun_BV_neg_boolean_valued
-- name    : BooleanFun.BV.neg_boolean_valued
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:11.887215+00:00
-- url     : https://prove2.me/theorems/4d5606b9-6e28-4883-a8e9-081a0644560f
-- title:
--   BV: neg boolean valued
-- statement:
--   The BV construction uses the neg boolean valued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L61-L62
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L61-L62

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.neg_boolean_valued (hbv : BooleanValued f) : BooleanValued (-f) := by sorry
