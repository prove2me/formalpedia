-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_dict_hasDegreeLE_one
-- name    : AaronsonAmbainis.Bridge.dict_hasDegreeLE_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:10.993685+00:00
-- url     : https://prove2.me/theorems/73e035c6-ab23-4714-9897-85dcdcd2ff6b
-- title:
--   Bridge: dict has Degree LE one
-- statement:
--   The Bridge construction uses the dict has Degree LE one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L134-L146
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L134-L146

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.dict_hasDegreeLE_one (j : ι) : HasDegreeLE (dict j) 1 := by sorry
