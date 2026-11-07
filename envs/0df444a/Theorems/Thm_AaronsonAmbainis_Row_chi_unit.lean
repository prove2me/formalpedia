-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_chi_unit
-- name    : AaronsonAmbainis.Row.chi_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:24.34933+00:00
-- url     : https://prove2.me/theorems/0db186f0-a748-4a76-a0c8-a6c6d31a84b9
-- title:
--   Row: chi unit
-- statement:
--   The Row construction uses the chi unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L45-L47
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L45-L47

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Row.chi_unit [DecidableEq ι] (U : Finset ι) (b : ι) :
    chi U (unit b) = if b ∈ U then -1 else 1 := by sorry
