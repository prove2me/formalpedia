-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_antipode_antipode
-- name    : AaronsonAmbainis.Bridge.antipode_antipode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:15.149379+00:00
-- url     : https://prove2.me/theorems/a5fb77ce-68ab-43f0-bdc7-ecc7f6f57177
-- title:
--   Bridge: antipode antipode
-- statement:
--   The Bridge construction uses the antipode antipode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L46-L48
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L46-L48

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.antipode_antipode (x : Cube ι) : antipode (antipode x) = x := by sorry
