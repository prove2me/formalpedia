-- Prove2me | Theorems.Thm_Comp_HideOrRun_hr_LF
-- name    : Comp.HideOrRun.hr_LF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:51:11.67226+00:00
-- url     : https://prove2.me/theorems/4a3d2c9c-2e4a-43f2-a4ed-a17fda5716ce
-- title:
--   Hide Or Run: hr LF
-- statement:
--   **The value-1 set of hide-or-run.** `live` can reach `goal` with probability arbitrarily close
--       to one, and `LF` says so -- through three nested fixed points, none of them given an iteration
--       bound, all of them run and checked.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L282-L283
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L282-L283

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

theorem Comp.HideOrRun.hr_LF : (game.toCSG game_wf).LF ↑target = (↑winning : Set HR) := by sorry
