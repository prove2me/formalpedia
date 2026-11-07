-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_mean_dict
-- name    : AaronsonAmbainis.Bridge.mean_dict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:01.85567+00:00
-- url     : https://prove2.me/theorems/6f499c3b-8731-45d5-84f9-86e4d7c285a3
-- title:
--   Bridge: mean dict
-- statement:
--   The Bridge construction uses the mean dict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L165-L166
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L165-L166

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.mean_dict (j : ι) : mean (dict j) = 0 := by sorry
