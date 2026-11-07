-- Prove2me | Theorems.Thm_AaronsonAmbainis_sum_allPairsTerm
-- name    : AaronsonAmbainis.sum_allPairsTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:39.269886+00:00
-- url     : https://prove2.me/theorems/55479ea3-0335-4417-9c21-80fb512364d5
-- title:
--   Aaronson Ambainis: sum all Pairs Term
-- statement:
--   The terms of `x` in all the inequalities `allPairs_core` are the terms of the pairs `(x, y)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L31-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L31-L40

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.sum_allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ) (x : Cube ι) :
    ∑ F : Finset ι, allPairsTerm g w lam F x
      = ∑ y, if g x = true ∧ g y = false then
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ else 0 := by sorry
