-- Prove2me | Theorems.Thm_BooleanFun_BV_VoteConsistent_comm_right
-- name    : BooleanFun.BV.VoteConsistent.comm_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:06:57.714178+00:00
-- url     : https://prove2.me/theorems/9cc5f0c3-9b50-4f9a-bf58-1f992139806d
-- title:
--   Vote Consistent: comm right
-- statement:
--   Commute arguments of `VoteConsistent` predicate
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L85-L88
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L85-L88

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV.VoteConsistent.comm_right {x y z : Votes n}:
    VoteConsistent x y z = VoteConsistent x z y := by sorry
