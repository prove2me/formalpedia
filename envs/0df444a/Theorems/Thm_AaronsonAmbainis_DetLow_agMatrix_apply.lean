-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_apply
-- name    : AaronsonAmbainis.DetLow.agMatrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:30.574976+00:00
-- url     : https://prove2.me/theorems/c1f137a0-d588-487f-a75d-3cbb01111ea5
-- title:
--   Det Low: ag Matrix apply
-- statement:
--   The Det Low construction uses the ag Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L71-L72
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L71-L72

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := by sorry
