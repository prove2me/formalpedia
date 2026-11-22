-- Prove2me | Theorems.Thm_Csg_homeWetSplit_wet
-- name    : Csg.homeWetSplit_wet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:57.189879+00:00
-- url     : https://prove2.me/theorems/ee7ca056-6394-408c-bb70-0bcf9b26b05d
-- title:
--   Csg: home Wet Split wet
-- statement:
--   The Csg construction uses the home Wet Split wet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L204-L205
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L204-L205

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.homeWetSplit_wet (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .wet = ENNReal.ofReal (1 - p) := by sorry
