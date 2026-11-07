-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_iff
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:53.142201+00:00
-- url     : https://prove2.me/theorems/ca9dd05a-d101-4f98-b445-87725217eb02
-- title:
--   Bridge: has Degree LE zero iff
-- statement:
--   Degree at most `0` is the same as constant.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L98-L120
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L98-L120

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_zero_iff {f : Cube ι → ℝ} : HasDegreeLE f 0 ↔ ∃ a : ℝ, ∀ x, f x = a := by sorry
