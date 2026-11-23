-- Prove2me | Theorems.Thm_Comp_HideOrRun_inner_at_winning
-- name    : Comp.HideOrRun.inner_at_winning
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:16.795911+00:00
-- url     : https://prove2.me/theorems/cc86aa80-bcce-424d-87b1-75ce84237628
-- title:
--   Hide Or Run: inner at winning
-- statement:
--   And the outer chain has stopped: `winning` is its own `μX` fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L275-L277
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L275-L277

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

theorem Comp.HideOrRun.inner_at_winning :
    ((game.toCSG game_wf).LFInner ↑target ↑winning).lfp = (↑winning : Set HR) := by sorry
