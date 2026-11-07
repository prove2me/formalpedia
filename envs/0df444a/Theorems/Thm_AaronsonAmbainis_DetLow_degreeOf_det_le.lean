-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_det_le
-- name    : AaronsonAmbainis.DetLow.degreeOf_det_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:53.363782+00:00
-- url     : https://prove2.me/theorems/37835ee0-8aa4-4a08-8fb6-98322fb2394c
-- title:
--   Det Low: degree Of det le
-- statement:
--   In the variable `s_j` the determinant of the agreement matrix has degree at most the number
--   of ones of `g` (proof of Lemma 3.6 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Degree.lean#L33-L47
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Degree.lean#L33-L47

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.degreeOf_det_le (g : Cube ι → Bool) (j : ι) :
    degreeOf j (agMatrix g).det ≤ Fintype.card (Ones g) := by sorry
