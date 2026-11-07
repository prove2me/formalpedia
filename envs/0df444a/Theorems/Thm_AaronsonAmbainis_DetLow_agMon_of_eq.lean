-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agMon_of_eq
-- name    : AaronsonAmbainis.DetLow.agMon_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:51.539717+00:00
-- url     : https://prove2.me/theorems/07715208-c9f9-47c0-b9a2-02534c38afcc
-- title:
--   Det Low: ag Mon of eq
-- statement:
--   If `x` and `z` agree at `j` then `M[x,z] = s_j * M[x^j,z]`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L35-L41
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L35-L41

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agMon_of_eq (x z : Cube ι) (j : ι) (h : x j = z j) :
    agMon x z = X j * agMon (flipSet x {j}) z := by sorry
