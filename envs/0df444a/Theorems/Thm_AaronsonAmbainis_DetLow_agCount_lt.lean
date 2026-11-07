-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_agCount_lt
-- name    : AaronsonAmbainis.DetLow.agCount_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:29.505686+00:00
-- url     : https://prove2.me/theorems/5065ef93-09af-4482-8348-8e284354da46
-- title:
--   Det Low: ag Count lt
-- statement:
--   The Det Low construction uses the ag Count lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L47-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L47-L53

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.agCount_lt (x z : Cube ι) (h : x ≠ z) : agCount x z < Fintype.card ι := by sorry
