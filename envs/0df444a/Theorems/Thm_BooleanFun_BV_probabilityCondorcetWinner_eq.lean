-- Prove2me | Theorems.Thm_BooleanFun_BV_probabilityCondorcetWinner_eq
-- name    : BooleanFun.BV.probabilityCondorcetWinner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:08:04.374231+00:00
-- url     : https://prove2.me/theorems/fc284d5f-0396-4911-b5b7-17a6c39e4251
-- title:
--   BV: probability Condorcet Winner eq
-- statement:
--   The probability of having a Condorcet winner can be expressed in terms of the noise operator.
--   See [odonnell2014], Theorem 2.56.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L239-L273
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L239-L273

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
local notation "T" => _Tnae3

theorem BooleanFun.BV.probabilityCondorcetWinner_eq (hbv : BooleanValued f) :
    probabilityCondorcetWinner f = 3/4 * (1- noise_stability (-1/3) f) := by sorry
