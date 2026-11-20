-- Prove2me | Theorems.Thm_BooleanFun_BV_oneOn_NAE3_eq
-- name    : BooleanFun.BV.oneOn_NAE3_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:07:24.847833+00:00
-- url     : https://prove2.me/theorems/10602e56-9850-4d51-935c-cb25c2394767
-- title:
--   BV: one On NAE3 eq
-- statement:
--   Explicit Walsh-Fourier expansion of the not-all-equal predicate on a 3-tuple composed with a Boolean valued function.
--   A crucial step in the proof of Arrow's theorem.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L120-L124
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L120-L124

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV.oneOn_NAE3_eq (hbv : BooleanValued f) {x y z : Fin n → Fin 2}:
    oneOn (NAE3 (f x) (f y) (f z)) = 3/4 - (1/4) * (f x) * (f y) - (1/4) * (f y) * (f z) - (1/4) * (f x) * (f z) := by sorry
