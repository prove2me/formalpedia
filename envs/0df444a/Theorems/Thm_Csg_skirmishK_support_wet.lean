-- Prove2me | Theorems.Thm_Csg_skirmishK_support_wet
-- name    : Csg.skirmishK_support_wet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:52:16.630331+00:00
-- url     : https://prove2.me/theorems/042083be-b2fc-4bab-8dc8-cbbc630d5039
-- title:
--   Csg: skirmish K support wet
-- statement:
--   **The payoff.** `wet`'s support, for any joint move -- the raw material `Pre1`/`A`/`B` will
--       unfold to whenever the current position is `wet`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L137-L139
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L137-L139

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_support_wet (a1 : SoldierMove) (a2 : SniperMove) :
    (skirmishCSG.K .wet a1 a2).support = {SkirmishPos.wet} := by sorry
