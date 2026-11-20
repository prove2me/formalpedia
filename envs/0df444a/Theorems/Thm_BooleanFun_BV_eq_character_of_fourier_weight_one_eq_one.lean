-- Prove2me | Theorems.Thm_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one
-- name    : BooleanFun.BV.eq_character_of_fourier_weight_one_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:31.861645+00:00
-- url     : https://prove2.me/theorems/7a91aeae-1904-43d6-88d3-f59e53f0b414
-- title:
--   BV: eq character of fourier weight one eq one
-- statement:
--   A Boolean valued function with degree one Fourier weight equal to one
--   must be `±1` times a degree one character.
--   This is [odonnell2014], Exercise 1.19(a).
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L237-L243
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L237-L243

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.eq_character_of_fourier_weight_one_eq_one (hbv : BooleanValued f) (hn : n>0)
    (hf : fourierWeight 1 f = 1):
    ∃ i, ∃ c : ℝ, f = c•χ {i} := by sorry
