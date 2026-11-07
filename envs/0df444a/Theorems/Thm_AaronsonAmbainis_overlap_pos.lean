-- Prove2me | Theorems.Thm_AaronsonAmbainis_overlap_pos
-- name    : AaronsonAmbainis.overlap_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:27.480649+00:00
-- url     : https://prove2.me/theorems/001cb2c7-2692-4f7b-b8c6-1d373df82651
-- title:
--   Aaronson Ambainis: overlap pos
-- statement:
--   Consequence of the overlap lemma: the weighted overlap is positive.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L72-L86
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L72-L86

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.overlap_pos {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < ∑ j ∈ diffSet p q, w j * x j * y j := by sorry
