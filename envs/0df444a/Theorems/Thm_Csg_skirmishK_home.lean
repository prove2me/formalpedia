-- Prove2me | Theorems.Thm_Csg_skirmishK_home
-- name    : Csg.skirmishK_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:29:30.124468+00:00
-- url     : https://prove2.me/theorems/2fa2bbc2-717e-4d2a-9561-73fb3c7e61a6
-- title:
--   Csg: skirmish K home
-- statement:
--   The Csg construction uses the skirmish K home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L124-L125
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L124-L125

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_home (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .home a1 a2 = PMF.pure .hide := by sorry
