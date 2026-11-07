-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_stp_intervalIntegrable
-- name    : AaronsonAmbainis.Level.stp_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:19.046325+00:00
-- url     : https://prove2.me/theorems/ea25ba2b-428f-4aee-9571-2a940b508734
-- title:
--   Level: stp interval Integrable
-- statement:
--   The Level construction uses the stp interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L90-L92
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L90-L92

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.stp_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (stp c) MeasureTheory.volume a b := by sorry
