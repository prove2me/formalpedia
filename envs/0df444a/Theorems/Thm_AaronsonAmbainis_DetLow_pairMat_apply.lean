-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_apply
-- name    : AaronsonAmbainis.DetLow.pairMat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:29.272451+00:00
-- url     : https://prove2.me/theorems/e250f33b-4138-435b-96e7-41251c897e00
-- title:
--   Det Low: pair Mat apply
-- statement:
--   The Det Low construction uses the pair Mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L67-L68
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L67-L68

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.pairMat_apply (g : Cube ι → Bool) (j : ι) (x y : Ones g) :
    pairMat g j x y = if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0 := by sorry
