-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_isEmpty
-- name    : AaronsonAmbainis.Level.variance_eq_zero_of_isEmpty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:47.952087+00:00
-- url     : https://prove2.me/theorems/87a197a7-6743-4545-a6b5-da7ffad4107e
-- title:
--   Level: variance eq zero of is Empty
-- statement:
--   On the empty index type every variance is `0`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L72-L73
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L72-L73

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.variance_eq_zero_of_isEmpty [IsEmpty ι] (f : Cube ι → ℝ) : variance f = 0 := by sorry
