-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_sub_mean
-- name    : AaronsonAmbainis.Level.sum_sub_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:24.555196+00:00
-- url     : https://prove2.me/theorems/0f460d58-a51b-421f-928f-c7c270fc94cc
-- title:
--   Level: sum sub mean
-- statement:
--   `E (f - E f) = 0`, unnormalised.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L76-L79
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L76-L79

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_sub_mean (f : Cube ι → ℝ) : ∑ x, (f x - mean f) = 0 := by sorry
