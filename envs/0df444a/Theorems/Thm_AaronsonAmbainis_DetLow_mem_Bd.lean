-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_mem_Bd
-- name    : AaronsonAmbainis.DetLow.mem_Bd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:13.676928+00:00
-- url     : https://prove2.me/theorems/29cbdf07-161b-4f0f-9b1c-876cc05a2e67
-- title:
--   Det Low: mem Bd
-- statement:
--   The Det Low construction uses the mem Bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L31-L33
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L31-L33

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.mem_Bd {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Bd g j ↔ g (flipSet x.1 {j}) = false := by sorry
