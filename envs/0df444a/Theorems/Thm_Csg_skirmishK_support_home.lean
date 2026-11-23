-- Prove2me | Theorems.Thm_Csg_skirmishK_support_home
-- name    : Csg.skirmishK_support_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:47:27.126848+00:00
-- url     : https://prove2.me/theorems/6619f9c2-f3b8-45ad-83ea-432281037462
-- title:
--   Csg: skirmish K support home
-- statement:
--   **The payoff.** `home`'s support, for any joint move.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L142-L144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L142-L144

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_home (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .home a1 a2).support = {SkirmishPos.hide} := by sorry
