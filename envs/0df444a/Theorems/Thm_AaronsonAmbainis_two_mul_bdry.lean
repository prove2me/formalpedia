-- Prove2me | Theorems.Thm_AaronsonAmbainis_two_mul_bdry
-- name    : AaronsonAmbainis.two_mul_bdry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:22.781329+00:00
-- url     : https://prove2.me/theorems/133cfa38-8b25-4257-9285-29274435d46b
-- title:
--   Aaronson Ambainis: two mul bdry
-- statement:
--   Lemma 2.1 of the paper: `2 b_j(g) = 2^n I_j(g)`, that is, `b_j(g) = 2^(n-1) I_j(g)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L124-L130
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Overlap.lean#L124-L130

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.two_mul_bdry (g : Cube ι → Bool) (j : ι) :
    2 * (bdry g j : ℝ) = 2 ^ Fintype.card ι * infl g j := by sorry
