-- Prove2me | Theorems.Thm_Csg_skirmishK_support_hide_run_wait
-- name    : Csg.skirmishK_support_hide_run_wait
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:52:33.838349+00:00
-- url     : https://prove2.me/theorems/159b678a-1d9d-41aa-8d25-0ed5b24db1ab
-- title:
--   Csg: skirmish K support hide run wait
-- statement:
--   **The payoff.** `hide`'s support against `(run,wait)`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L157-L159
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L157-L159

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_hide_run_wait :
    (skirmishCSG.K .hide .run .wait).support = {SkirmishPos.home} := by sorry
