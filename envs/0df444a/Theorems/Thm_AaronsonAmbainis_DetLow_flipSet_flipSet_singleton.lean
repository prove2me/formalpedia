-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
-- name    : AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:19.621818+00:00
-- url     : https://prove2.me/theorems/a13234e2-9e70-4e5b-8e2d-42838ed933da
-- title:
--   Det Low: flip Set flip Set singleton
-- statement:
--   The Det Low construction uses the flip Set flip Set singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L39-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L39-L44

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetLow.flipSet_flipSet_singleton (x : Cube ι) (j : ι) :
    flipSet (flipSet x {j}) {j} = x := by sorry
