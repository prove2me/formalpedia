-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_of_ne
-- name    : AaronsonAmbainis.DetLow.flipSet_singleton_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:51.631554+00:00
-- url     : https://prove2.me/theorems/ca6d4fd4-33e1-4fc1-87f3-2be63f4dceb2
-- title:
--   Det Low: flip Set singleton of ne
-- statement:
--   The Det Low construction uses the flip Set singleton of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L34-L36
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L34-L36

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetLow.flipSet_singleton_of_ne (x : Cube ι) {i j : ι} (h : i ≠ j) :
    flipSet x {j} i = x i := by sorry
