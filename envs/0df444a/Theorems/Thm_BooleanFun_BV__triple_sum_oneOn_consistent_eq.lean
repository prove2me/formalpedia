-- Prove2me | Theorems.Thm_BooleanFun_BV__triple_sum_oneOn_consistent_eq
-- name    : BooleanFun.BV._triple_sum_oneOn_consistent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:02.485961+00:00
-- url     : https://prove2.me/theorems/e899797f-32b5-4536-8d2d-b27a54e0dab3
-- title:
--   BV: triple sum one On consistent eq
-- statement:
--   Auxiliary lemma for the proof of `probabilityCondorcetWinner_eq_one`
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L135-L147
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L135-L147

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV._triple_sum_oneOn_consistent_eq:
    ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z) = 6^n := by sorry
