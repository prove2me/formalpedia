-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_dict
-- name    : AaronsonAmbainis.Bridge.variance_dict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:48.427745+00:00
-- url     : https://prove2.me/theorems/803c08c3-5da0-4e24-bba5-c459fea930de
-- title:
--   Bridge: variance dict
-- statement:
--   The Bridge construction uses the variance dict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L168-L172
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L168-L172

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.variance_dict (j : ι) : variance (dict j) = 1 := by sorry
