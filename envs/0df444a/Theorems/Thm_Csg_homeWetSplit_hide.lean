-- Prove2me | Theorems.Thm_Csg_homeWetSplit_hide
-- name    : Csg.homeWetSplit_hide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:52:16.169924+00:00
-- url     : https://prove2.me/theorems/7e531245-11a1-4e89-bfa1-31aa42d93972
-- title:
--   Csg: home Wet Split hide
-- statement:
--   The Csg construction uses the home Wet Split hide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L207-L208
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L207-L208

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.homeWetSplit_hide (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .hide = 0 := by sorry
