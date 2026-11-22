-- Prove2me | Theorems.Thm_Csg_skirmishK_wet
-- name    : Csg.skirmishK_wet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:29:24.738706+00:00
-- url     : https://prove2.me/theorems/81028043-cde1-40dd-8e8e-a1fb24ccc6e0
-- title:
--   Csg: skirmish K wet
-- statement:
--   The Csg construction uses the skirmish K wet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L121-L122
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L121-L122

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_wet (a1 : SoldierMove) (a2 : SniperMove) :
    skirmishCSG.K .wet a1 a2 = PMF.pure .wet := by sorry
