-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agMon_eq_mul_erase
-- name    : AaronsonAmbainis.DetLow.agMon_eq_mul_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:21.037548+00:00
-- url     : https://prove2.me/theorems/8d16591d-2b44-4a23-afe6-2b00aa320177
-- title:
--   Det Low: ag Mon eq mul erase
-- statement:
--   Splitting off the `j`-th factor of `agMon`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L21-L25
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L21-L25

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agMon_eq_mul_erase (x z : Cube ι) (j : ι) :
    agMon x z = (if x j = z j then X j else 1) *
      ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by sorry
