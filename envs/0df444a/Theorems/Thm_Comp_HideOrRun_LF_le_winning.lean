-- Prove2me | Theorems.Thm_Comp_HideOrRun_LF_le_winning
-- name    : Comp.HideOrRun.LF_le_winning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:00:57.9682+00:00
-- url     : https://prove2.me/theorems/b56ae7cf-26c1-48d9-8334-aa58d40c327b
-- title:
--   Hide Or Run: LF le winning
-- statement:
--   …which makes `winning` an upper bound on `LF target`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L270-L272
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L270-L272

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

theorem Comp.HideOrRun.LF_le_winning : (game.toCSG game_wf).LF ↑target ≤ (↑winning : Set HR) := by sorry
