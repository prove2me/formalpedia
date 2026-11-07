-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_unipotent_mul
-- name    : AaronsonAmbainis.DetLow.unipotent_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:38.823189+00:00
-- url     : https://prove2.me/theorems/c402787e-caae-4a56-93b1-215cd87c035d
-- title:
--   Det Low: unipotent mul
-- statement:
--   The Det Low construction uses the unipotent mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L118-L124
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L118-L124

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.unipotent_mul (g : Cube ι → Bool) (j : ι) :
    (1 + (X j : MvPolynomial ι ℤ) • pairMat g j) * (1 - (X j : MvPolynomial ι ℤ) • pairMat g j)
      = 1 := by sorry
