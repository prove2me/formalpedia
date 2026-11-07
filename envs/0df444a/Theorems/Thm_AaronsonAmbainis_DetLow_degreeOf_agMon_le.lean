-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_agMon_le
-- name    : AaronsonAmbainis.DetLow.degreeOf_agMon_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:53.877007+00:00
-- url     : https://prove2.me/theorems/c4786ca7-84d2-4ce3-a871-e3fb8396b87a
-- title:
--   Det Low: degree Of ag Mon le
-- statement:
--   Each entry of the agreement matrix has degree at most one in each variable.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Degree.lean#L18-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Degree.lean#L18-L29

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.degreeOf_agMon_le (x z : Cube ι) (j : ι) : degreeOf j (agMon x z) ≤ 1 := by sorry
