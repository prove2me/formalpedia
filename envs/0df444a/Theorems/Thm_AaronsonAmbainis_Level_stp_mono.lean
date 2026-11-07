-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_stp_mono
-- name    : AaronsonAmbainis.Level.stp_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:34.842088+00:00
-- url     : https://prove2.me/theorems/4c798039-6f10-4d5a-8378-8917d1550905
-- title:
--   Level: stp mono
-- statement:
--   The Level construction uses the stp mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L82-L88
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L82-L88

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.stp_mono (c : ℝ) : Monotone (stp c) := by sorry
