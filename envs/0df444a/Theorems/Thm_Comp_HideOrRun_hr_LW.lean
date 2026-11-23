-- Prove2me | Theorems.Thm_Comp_HideOrRun_hr_LW
-- name    : Comp.HideOrRun.hr_LW
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:50:13.146678+00:00
-- url     : https://prove2.me/theorems/f865860f-888f-4594-a444-8b1a7fd48a49
-- title:
--   Hide Or Run: hr LW
-- statement:
--   `LW`, for every pair of regions and state at once.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L182-L185
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L182-L185

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

theorem Comp.HideOrRun.hr_LW (x y : Finset HR) (s : HR) :
    (game.toCSG game_wf).LW ↑x ↑y s = (↑(lwC x y s) : Set Bool) := by sorry
