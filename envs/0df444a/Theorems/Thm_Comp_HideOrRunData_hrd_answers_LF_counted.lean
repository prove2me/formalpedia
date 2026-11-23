-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_answers_LF_counted
-- name    : Comp.HideOrRunData.hrd_answers_LF_counted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:49.273947+00:00
-- url     : https://prove2.me/theorems/1a712874-272b-47de-b281-ac2f687791e4
-- title:
--   Hide Or Run Data: hrd answers LF counted
-- statement:
--   The counted form of the same statement, kept so the build checks both routes agree.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L168-L171
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L168-L171

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
set_option maxRecDepth 4000

theorem Comp.HideOrRunData.hrd_answers_LF_counted :
    hrd.toCsgQ.Answers hrd_wf (Objective.limitReach hrdTarget) (Answer.region hrdWinning) := by sorry
