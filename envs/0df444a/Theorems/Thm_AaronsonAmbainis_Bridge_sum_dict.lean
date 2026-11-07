-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sum_dict
-- name    : AaronsonAmbainis.Bridge.sum_dict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:07.203992+00:00
-- url     : https://prove2.me/theorems/1ee815da-8bbb-4987-89ca-7ce0d79f4b7c
-- title:
--   Bridge: sum dict
-- statement:
--   The Bridge construction uses the sum dict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L157-L163
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L157-L163

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.sum_dict (j : ι) : ∑ x : Cube ι, dict j x = 0 := by sorry
