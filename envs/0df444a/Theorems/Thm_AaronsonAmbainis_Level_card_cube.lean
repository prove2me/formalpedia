-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_card_cube
-- name    : AaronsonAmbainis.Level.card_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:20.360728+00:00
-- url     : https://prove2.me/theorems/94a43834-9759-4275-a17f-2fd4475f4168
-- title:
--   Level: card cube
-- statement:
--   The cube has `2 ^ n` points.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L35-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L35-L40

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Theorems.Thm_AaronsonAmbainis_card_cube

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.card_cube : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by sorry
