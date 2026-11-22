-- Prove2me | Theorems.Thm_Csg_skirmishK_hide_hide_throw
-- name    : Csg.skirmishK_hide_hide_throw
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:29:51.576831+00:00
-- url     : https://prove2.me/theorems/733b8df2-db97-4fef-b03a-b1d843a75eb8
-- title:
--   Csg: skirmish K hide hide throw
-- statement:
--   The Csg construction uses the skirmish K hide hide throw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L129-L129
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Skirmish.lean#L129-L129

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_Skirmish
set_option autoImplicit true
open Csg

theorem Csg.skirmishK_hide_hide_throw : skirmishCSG.K .hide .hide .throw = PMF.pure .home := by sorry
