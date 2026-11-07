-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_antipodal_iff_onZone
-- name    : AaronsonAmbainis.Bridge.antipodal_iff_onZone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:29:54.655103+00:00
-- url     : https://prove2.me/theorems/e0f28f9e-d30e-4937-a691-17a084afd14b
-- title:
--   Bridge: antipodal iff on Zone
-- statement:
--   The Bridge construction uses the antipodal iff on Zone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L124-L153
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L124-L153

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.antipodal_iff_onZone : AntipodalInequality ↔ AntipodalOnZone := by sorry
