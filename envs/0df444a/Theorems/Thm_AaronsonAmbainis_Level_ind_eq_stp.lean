-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_ind_eq_stp
-- name    : AaronsonAmbainis.Level.ind_eq_stp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:25.802119+00:00
-- url     : https://prove2.me/theorems/02eb2417-e67b-431d-87ab-1fa9e0bba6a0
-- title:
--   Level: ind eq stp
-- statement:
--   The indicator of `[p, q)` as a difference of two step functions.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L114-L123
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L114-L123

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.ind_eq_stp (p q t : ℝ) :
    (if p ≤ t ∧ t < q then (1 : ℝ) else 0) = stp p t - stp (max p q) t := by sorry
