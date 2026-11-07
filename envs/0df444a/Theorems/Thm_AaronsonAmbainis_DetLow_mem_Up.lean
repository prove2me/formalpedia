-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_mem_Up
-- name    : AaronsonAmbainis.DetLow.mem_Up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:08.742627+00:00
-- url     : https://prove2.me/theorems/5a6d7976-7b3f-4098-885b-4dec6b766633
-- title:
--   Det Low: mem Up
-- statement:
--   The Det Low construction uses the mem Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L24-L26
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Basic.lean#L24-L26

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.mem_Up {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Up g j ↔ x.1 j = true ∧ g (flipSet x.1 {j}) = true := by sorry
