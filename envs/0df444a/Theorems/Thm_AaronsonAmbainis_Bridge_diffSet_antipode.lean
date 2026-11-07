-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_antipode
-- name    : AaronsonAmbainis.Bridge.diffSet_antipode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:59.210727+00:00
-- url     : https://prove2.me/theorems/3d927433-a354-4d9b-b0df-e127839c640a
-- title:
--   Bridge: diff Set antipode
-- statement:
--   The Bridge construction uses the diff Set antipode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L41-L43
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L41-L43

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.diffSet_antipode (u : Cube ι) : diffSet u (antipode u) = univ := by sorry
