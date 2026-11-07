-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_variance_nonneg
-- name    : AaronsonAmbainis.Level.variance_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:43.947924+00:00
-- url     : https://prove2.me/theorems/e035caba-70d3-42d6-b520-cc441271e3ee
-- title:
--   Level: variance nonneg
-- statement:
--   The Level construction uses the variance nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L57-L59
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L57-L59

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.variance_nonneg (f : Cube ι → ℝ) : 0 ≤ variance f := by sorry
