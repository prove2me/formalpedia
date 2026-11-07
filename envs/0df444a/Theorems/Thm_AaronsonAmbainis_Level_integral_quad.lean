-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_integral_quad
-- name    : AaronsonAmbainis.Level.integral_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:31.838806+00:00
-- url     : https://prove2.me/theorems/f79b491a-4037-4750-a04a-45c95a56c30e
-- title:
--   Level: integral quad
-- statement:
--   `∫_v^u (u - t)(t - v) dt = (u - v)^3 / 6`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L19-L35
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L19-L35

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.integral_quad (v u : ℝ) : ∫ t in v..u, (u - t) * (t - v) = (u - v) ^ 3 / 6 := by sorry
