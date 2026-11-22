-- Prove2me | Theorems.Thm_Csg_homeWetSplit_home
-- name    : Csg.homeWetSplit_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:28.404675+00:00
-- url     : https://prove2.me/theorems/6c0769c5-03f5-495d-b9a7-8ad88b5f7442
-- title:
--   Csg: home Wet Split home
-- statement:
--   The Csg construction uses the home Wet Split home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L201-L202
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishFeint.lean#L201-L202

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
set_option autoImplicit true
open Csg

theorem Csg.homeWetSplit_home (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    homeWetSplit p hp0 hp1 .home = ENNReal.ofReal p := by sorry
