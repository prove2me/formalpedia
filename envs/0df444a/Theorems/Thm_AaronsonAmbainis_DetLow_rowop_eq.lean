-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_rowop_eq
-- name    : AaronsonAmbainis.DetLow.rowop_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:38.710448+00:00
-- url     : https://prove2.me/theorems/f4c5b156-e7e9-4eab-86ac-7930514a5633
-- title:
--   Det Low: rowop eq
-- statement:
--   The Det Low construction uses the rowop eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L126-L141
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L126-L141

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.rowop_eq (g : Cube ι → Bool) (j : ι) :
    (1 - (X j : MvPolynomial ι ℤ) • pairMat g j) * agMatrix g
      = Matrix.diagonal (diagVec g j) * redMat g j := by sorry
