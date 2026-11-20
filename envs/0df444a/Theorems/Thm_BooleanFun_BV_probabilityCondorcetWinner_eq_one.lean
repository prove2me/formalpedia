-- Prove2me | Theorems.Thm_BooleanFun_BV_probabilityCondorcetWinner_eq_one
-- name    : BooleanFun.BV.probabilityCondorcetWinner_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:07:28.630962+00:00
-- url     : https://prove2.me/theorems/8d38bae2-4111-4505-9770-960dc1fcab64
-- title:
--   BV: probability Condorcet Winner eq one
-- statement:
--   If a voting rule is Condorcet, then the probability of a Condorcet winner equals 1.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L150-L160
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L150-L160

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}

theorem BooleanFun.BV.probabilityCondorcetWinner_eq_one (hc : IsCondorcet f):
    probabilityCondorcetWinner f = 1 := by sorry
