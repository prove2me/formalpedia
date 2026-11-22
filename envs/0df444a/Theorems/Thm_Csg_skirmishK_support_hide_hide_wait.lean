-- Prove2me | Theorems.Thm_Csg_skirmishK_support_hide_hide_wait
-- name    : Csg.skirmishK_support_hide_hide_wait
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:33.63122+00:00
-- url     : https://prove2.me/theorems/6a33aae6-9e84-4729-b353-480761c7cc87
-- title:
--   Csg: skirmish K support hide hide wait
-- statement:
--   **The payoff.** `hide`'s support against `(hide,wait)`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L147-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L147-L149

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_hide_hide_wait :
    (skirmishCSG.K .hide .hide .wait).support = {SkirmishPos.hide} := by sorry
