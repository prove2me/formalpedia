-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_dict_sq
-- name    : AaronsonAmbainis.Bridge.dict_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:47.085204+00:00
-- url     : https://prove2.me/theorems/1a1fb60a-e117-41f4-819f-77041ac34f6a
-- title:
--   Bridge: dict sq
-- statement:
--   The Bridge construction uses the dict sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L48-L50
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L48-L50

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Bridge.dict_sq (j : ι) (x : Cube ι) : dict j x ^ 2 = 1 := by sorry
