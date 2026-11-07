-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_bdry_lev
-- name    : AaronsonAmbainis.Level.bdry_lev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:32.670951+00:00
-- url     : https://prove2.me/theorems/6bf10ae5-8b79-48ed-aa7e-3094a78b7f13
-- title:
--   Level: bdry lev
-- statement:
--   `b_j(g_t)` is the number of points `x` with `f(x^j) ≤ t < f(x)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L110-L119
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L110-L119

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.bdry_lev (f : Cube ι → ℝ) (t : ℝ) (j : ι) :
    (bdry (lev f t) j : ℝ)
      = ∑ x, if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0 := by sorry
