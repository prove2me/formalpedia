-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_indicator
-- name    : AaronsonAmbainis.Row.hasDegreeLE_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:45.473195+00:00
-- url     : https://prove2.me/theorems/bb9c1a31-294a-498f-8166-eb185d0dac47
-- title:
--   Row: has Degree LE indicator
-- statement:
--   The indicator of a coordinate has degree at most `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L145-L151
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L145-L151

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_indicator (b : β) :
    HasDegreeLE (fun w : Cube β => if w b then (1 : ℝ) else 0) 1 := by sorry
