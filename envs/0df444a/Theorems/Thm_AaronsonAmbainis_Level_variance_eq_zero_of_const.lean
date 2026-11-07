-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_variance_eq_zero_of_const
-- name    : AaronsonAmbainis.Level.variance_eq_zero_of_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:31.497257+00:00
-- url     : https://prove2.me/theorems/7146ca70-ca84-4804-8028-c80057d1df2e
-- title:
--   Level: variance eq zero of const
-- statement:
--   A function with all values equal has variance zero.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L62-L69
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L62-L69

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.variance_eq_zero_of_const (f : Cube ι → ℝ) (h : ∀ x y, f x = f y) : variance f = 0 := by sorry
