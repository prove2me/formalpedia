-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_const
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_zero_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:03.187603+00:00
-- url     : https://prove2.me/theorems/5c864ed1-8522-456a-9830-b2db6089bc63
-- title:
--   Bridge: has Degree LE zero const
-- statement:
--   `HasDegreeLE f 0` implies `f` constant.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L123-L126
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L123-L126

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_zero_const {f : Cube ι → ℝ} (h : HasDegreeLE f 0) (x y : Cube ι) :
    f x = f y := by sorry
