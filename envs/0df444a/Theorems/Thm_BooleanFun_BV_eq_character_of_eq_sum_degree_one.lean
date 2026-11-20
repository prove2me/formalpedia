-- Prove2me | Theorems.Thm_BooleanFun_BV_eq_character_of_eq_sum_degree_one
-- name    : BooleanFun.BV.eq_character_of_eq_sum_degree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:19.629407+00:00
-- url     : https://prove2.me/theorems/7c0e37c9-f0b8-443b-a514-878d94be43f7
-- title:
--   BV: eq character of eq sum degree one
-- statement:
--   A Boolean valued function that is a linear combination of degree one characters must be constant
--   times a degree one character.
--   Most involved step towards `eq_character_of_fourier_weight_one_eq_one`.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L73-L222
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/BooleanValued.lean#L73-L222

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV

theorem BooleanFun.BV.eq_character_of_eq_sum_degree_one (hbv : BooleanValued f) (hn : n>0)
    (hf : ∀ x, f x = ∑ i, 𝓕 f {i} * (-1)^(x i).val):
    ∃ S ∈ {S|S.card = 1}, ∃ c : ℝ, f = c•χ S := by sorry
