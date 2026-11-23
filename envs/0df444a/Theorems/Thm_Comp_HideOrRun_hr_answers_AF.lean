-- Prove2me | Theorems.Thm_Comp_HideOrRun_hr_answers_AF
-- name    : Comp.HideOrRun.hr_answers_AF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:59.457358+00:00
-- url     : https://prove2.me/theorems/482f77d4-bdc1-411e-994d-99f848e5da87
-- title:
--   Hide Or Run: hr answers AF
-- statement:
--   The Hide Or Run construction uses the hr answers AF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L370-L372
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L370-L372

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun

theorem Comp.HideOrRun.hr_answers_AF :
    game.Answers game_wf (Objective.almostReach target) (Answer.region target) := by sorry
