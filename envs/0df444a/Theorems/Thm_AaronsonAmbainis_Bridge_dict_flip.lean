-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_dict_flip
-- name    : AaronsonAmbainis.Bridge.dict_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:58.182872+00:00
-- url     : https://prove2.me/theorems/83c83bba-46cb-4d7a-a851-811ec2806a06
-- title:
--   Bridge: dict flip
-- statement:
--   The Bridge construction uses the dict flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L52-L55
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L52-L55

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*}

theorem AaronsonAmbainis.Bridge.dict_flip [DecidableEq ι] (j : ι) (x : Cube ι) : dict j (flipSet x {j}) = -dict j x := by sorry
