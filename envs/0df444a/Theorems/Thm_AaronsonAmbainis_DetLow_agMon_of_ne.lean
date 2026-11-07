-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agMon_of_ne
-- name    : AaronsonAmbainis.DetLow.agMon_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:28.354551+00:00
-- url     : https://prove2.me/theorems/5202c363-373c-4462-bf73-7e959f95e879
-- title:
--   Det Low: ag Mon of ne
-- statement:
--   If `x` and `z` disagree at `j` then `M[x^j,z] = s_j * M[x,z]`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L44-L51
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L44-L51

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agMon_of_ne (x z : Cube ι) (j : ι) (h : x j ≠ z j) :
    agMon (flipSet x {j}) z = X j * agMon x z := by sorry
