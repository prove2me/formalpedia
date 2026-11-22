-- Prove2me | Theorems.Thm_Csg_skirmishK_support_hide_run_throw
-- name    : Csg.skirmishK_support_hide_run_throw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:52:42.548563+00:00
-- url     : https://prove2.me/theorems/ded38e37-3327-4466-a0a3-958171303481
-- title:
--   Csg: skirmish K support hide run throw
-- statement:
--   **The payoff.** `hide`'s support against `(run,throw)`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L162-L164
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L162-L164

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_hide_run_throw :
    (skirmishCSG.K .hide .run .throw).support = {SkirmishPos.wet} := by sorry
