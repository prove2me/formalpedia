-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_dict_not_hasDegreeLE_zero
-- name    : AaronsonAmbainis.Bridge.dict_not_hasDegreeLE_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:53.391716+00:00
-- url     : https://prove2.me/theorems/b3dfa738-9207-41d9-bda7-3f260e37aec2
-- title:
--   Bridge: dict not has Degree LE zero
-- statement:
--   A dictator does not have degree at most `0`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L149-L155
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L149-L155

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.dict_not_hasDegreeLE_zero (j : ι) : ¬ HasDegreeLE (dict j) 0 := by sorry
