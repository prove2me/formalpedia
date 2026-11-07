-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_prod_diagVec
-- name    : AaronsonAmbainis.DetLow.prod_diagVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:40.771042+00:00
-- url     : https://prove2.me/theorems/f60181ee-6688-4b45-b0ae-8bae45ef8f0b
-- title:
--   Det Low: prod diag Vec
-- statement:
--   The Det Low construction uses the prod diag Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L143-L146
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L143-L146

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.prod_diagVec (g : Cube ι → Bool) (j : ι) :
    ∏ x, diagVec g j x = (1 - X j ^ 2) ^ (Up g j).card := by sorry
