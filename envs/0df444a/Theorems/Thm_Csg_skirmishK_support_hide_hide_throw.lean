-- Prove2me | Theorems.Thm_Csg_skirmishK_support_hide_hide_throw
-- name    : Csg.skirmishK_support_hide_hide_throw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:33.074261+00:00
-- url     : https://prove2.me/theorems/f52f5997-4554-433d-a375-a78d422519e7
-- title:
--   Csg: skirmish K support hide hide throw
-- statement:
--   **The payoff.** `hide`'s support against `(hide,throw)`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L152-L154
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L152-L154

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_hide_hide_throw :
    (skirmishCSG.K .hide .hide .throw).support = {SkirmishPos.home} := by sorry
