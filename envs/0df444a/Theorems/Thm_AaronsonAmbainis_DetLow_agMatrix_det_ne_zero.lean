-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_det_ne_zero
-- name    : AaronsonAmbainis.DetLow.agMatrix_det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:43.655184+00:00
-- url     : https://prove2.me/theorems/00782e6f-7160-4231-83b3-04f4ec59a83b
-- title:
--   Det Low: ag Matrix det ne zero
-- statement:
--   Lemma 3.4 of the paper: the determinant of the agreement matrix is nonzero.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L109-L114
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L109-L114

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agMatrix_det_ne_zero (g : Cube ι → Bool) : (agMatrix g).det ≠ 0 := by sorry
