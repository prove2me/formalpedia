-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
-- name    : AaronsonAmbainis.DetLow.flipSet_singleton_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:18.41762+00:00
-- url     : https://prove2.me/theorems/691f89a4-a559-4004-b428-362db69b8ff4
-- title:
--   Det Low: flip Set singleton self
-- statement:
--   The Det Low construction uses the flip Set singleton self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L29-L31
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L29-L31

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetLow.flipSet_singleton_self (x : Cube ι) (j : ι) :
    flipSet x {j} j = !(x j) := by sorry
