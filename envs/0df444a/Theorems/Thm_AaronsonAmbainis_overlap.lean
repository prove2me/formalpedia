-- Prove2me | Theorems.Thm_AaronsonAmbainis_overlap
-- name    : AaronsonAmbainis.overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:15.766194+00:00
-- url     : https://prove2.me/theorems/85691aca-b75f-45e4-b02d-8d4c5f115110
-- title:
--   Aaronson Ambainis: overlap
-- statement:
--   The overlap lemma (Lemma 4.1 of the paper): rows at points with different values overlap on
--   the difference set.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L18-L69
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L18-L69

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.overlap {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) :
    1 ≤ ∑ j ∈ diffSet p q, min (x j) (y j) := by sorry
