-- Prove2me | Theorems.Thm_Csg_skirmishK_hide_run_wait
-- name    : Csg.skirmishK_hide_run_wait
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:29:55.595195+00:00
-- url     : https://prove2.me/theorems/22e52d1b-24b0-47f2-85ef-f6b2b6367216
-- title:
--   Csg: skirmish K hide run wait
-- statement:
--   The Csg construction uses the skirmish K hide run wait property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L131-L131
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L131-L131

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_hide_run_wait : skirmishCSG.K .hide .run .wait = PMF.pure .home := by sorry
