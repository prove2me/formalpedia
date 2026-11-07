-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_allPairs_inner_pos
-- name    : AaronsonAmbainis.Bridge.allPairs_inner_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:29:25.56819+00:00
-- url     : https://prove2.me/theorems/e026f980-ab49-45c3-bd20-04b2b524e46e
-- title:
--   Bridge: all Pairs inner pos
-- statement:
--   No junk value in `AllPairsInequality`: for a one `x` and a zero `y` of `g` the inner sum is
--   positive.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L78-L85
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L78-L85

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.allPairs_inner_pos {g : Cube ι → Bool} {x y : Cube ι} (hx : g x = true) (hy : g y = false)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g x (lam x)) (h2 : IsRow g y (lam y)) :
    0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by sorry
