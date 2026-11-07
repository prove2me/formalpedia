-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_mul_agMatrix
-- name    : AaronsonAmbainis.DetLow.pairMat_mul_agMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:29.939648+00:00
-- url     : https://prove2.me/theorems/0c5696bb-49e9-4bb5-b00e-375665ba3557
-- title:
--   Det Low: pair Mat mul ag Matrix
-- statement:
--   The Det Low construction uses the pair Mat mul ag Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L92-L116
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L92-L116

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.pairMat_mul_agMatrix (g : Cube ι → Bool) (j : ι) (x z : Ones g) :
    (pairMat g j * agMatrix g) x z =
      if x ∈ Up g j then agMon (flipSet x.1 {j}) z.1 else 0 := by sorry
