-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_row_norm_ge_one
-- name    : AaronsonAmbainis.Bridge.row_norm_ge_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:29:37.87108+00:00
-- url     : https://prove2.me/theorems/9e587e27-da0c-4703-9fb3-f009330b92e6
-- title:
--   Bridge: row norm ge one
-- statement:
--   No junk value in `TwoSidedInequality`: if `g` takes another value somewhere, every row at
--   `x` has total weight at least `1` (Lemma 2.4 (ii) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L89-L96
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L89-L96

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.row_norm_ge_one {g : Cube ι → Bool} {x y : Cube ι} (hxy : g y ≠ g x) {lam : ι → ℝ}
    (h : IsRow g x lam) : 1 ≤ ∑ j, lam j := by sorry
