-- Prove2me | Theorems.Thm_AaronsonAmbainis_antipode_eq_flipSet_univ
-- name    : AaronsonAmbainis.antipode_eq_flipSet_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:32.444988+00:00
-- url     : https://prove2.me/theorems/3998faa0-757f-4ef1-8f9f-7fff849f93bd
-- title:
--   Aaronson Ambainis: antipode eq flip Set univ
-- statement:
--   The Aaronson Ambainis construction uses the antipode eq flip Set univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L30-L32
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L30-L32

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by sorry
