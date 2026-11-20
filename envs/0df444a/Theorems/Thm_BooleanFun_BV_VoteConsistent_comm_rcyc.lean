-- Prove2me | Theorems.Thm_BooleanFun_BV_VoteConsistent_comm_rcyc
-- name    : BooleanFun.BV.VoteConsistent.comm_rcyc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:07:07.944936+00:00
-- url     : https://prove2.me/theorems/60df1fa2-2fd8-4b2d-86ca-d0f50d3bc01e
-- title:
--   Vote Consistent: comm rcyc
-- statement:
--   Commute arguments of `VoteConsistent` predicate
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L91-L94
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L91-L94

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV.VoteConsistent.comm_rcyc {x y z : Votes n}:
    VoteConsistent x y z = VoteConsistent y z x := by sorry
