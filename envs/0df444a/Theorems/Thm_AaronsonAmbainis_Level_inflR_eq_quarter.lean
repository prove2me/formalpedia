-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_inflR_eq_quarter
-- name    : AaronsonAmbainis.Level.inflR_eq_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:37.423196+00:00
-- url     : https://prove2.me/theorems/349968ba-8140-42b6-a1a0-7d7689616595
-- title:
--   Level: infl R eq quarter
-- statement:
--   `inflR` is one quarter of the unnormalised L2 influence `E[(f(x) - f(x^j))^2]`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L104-L110
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L104-L110

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.inflR_eq_quarter (f : Cube ι → ℝ) (j : ι) :
    inflR f j = (∑ x, (f x - f (flipSet x {j})) ^ 2) / 2 ^ Fintype.card ι / 4 := by sorry
