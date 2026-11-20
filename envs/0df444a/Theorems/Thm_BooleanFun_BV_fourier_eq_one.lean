-- Prove2me | Theorems.Thm_BooleanFun_BV_fourier_eq_one
-- name    : BooleanFun.BV.fourier_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:05:30.77455+00:00
-- url     : https://prove2.me/theorems/927d5337-3fcc-42ef-9406-38e566eb58ca
-- title:
--   BV: fourier eq one
-- statement:
--   The BV construction uses the fourier eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L51-L53
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L51-L53

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.fourier_eq_one (hbv : BooleanValued f) : ∑ S, |𝓕 f S|^2 = 1 := by sorry
