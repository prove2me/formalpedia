-- Prove2me | Theorems.Thm_Comp_HideOrRun_hr_AF
-- name    : Comp.HideOrRun.hr_AF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:51:12.370579+00:00
-- url     : https://prove2.me/theorems/69b34656-a5d3-4c66-90dd-5d7d01a5d687
-- title:
--   Hide Or Run: hr AF
-- statement:
--   **Almost-sure reachability gets a strictly smaller answer**: the goal alone.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L346-L347
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L346-L347

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

theorem Comp.HideOrRun.hr_AF : (game.toCSG game_wf).AF ↑target = (↑target : Set HR) := by sorry
