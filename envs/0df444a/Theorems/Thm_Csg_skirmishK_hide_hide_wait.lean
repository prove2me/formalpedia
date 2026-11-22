-- Prove2me | Theorems.Thm_Csg_skirmishK_hide_hide_wait
-- name    : Csg.skirmishK_hide_hide_wait
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:29:52.606807+00:00
-- url     : https://prove2.me/theorems/46a6a5a2-15c2-4d6c-b048-d42bac3b92e2
-- title:
--   Csg: skirmish K hide hide wait
-- statement:
--   The Csg construction uses the skirmish K hide hide wait property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L127-L127
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L127-L127

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_hide_hide_wait : skirmishCSG.K .hide .hide .wait = PMF.pure .hide := by sorry
