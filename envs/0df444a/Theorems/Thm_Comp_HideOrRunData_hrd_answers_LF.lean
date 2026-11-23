-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_answers_LF
-- name    : Comp.HideOrRunData.hrd_answers_LF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:23:30.048019+00:00
-- url     : https://prove2.me/theorems/17a1f184-4e2a-471d-aeea-9feef17354cd
-- title:
--   Hide Or Run Data: hrd answers LF
-- statement:
--   **The value-1 set, from the model.** One `decide`, naming the region.
--
--       This is the line the whole loop exercise was for. Driving it by hand costs `hrd_lw` -- 192
--       `decide` instances at three states, and `2 ^ 30` at thirty -- plus an iteration count at each of
--       three nested levels. Here the three loops find their own fixed points and the caller says only
--       what came back.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L158-L161
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L158-L161

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_answers_LF :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) := by sorry
