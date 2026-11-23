-- Prove2me | Theorems.Thm_Comp_HideOrRun_AF_le_target
-- name    : Comp.HideOrRun.AF_le_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:02:25.886102+00:00
-- url     : https://prove2.me/theorems/a5a241b2-9e31-48d4-aeb8-cc6c09b00d45
-- title:
--   Hide Or Run: AF le target
-- statement:
--   The Hide Or Run construction uses the AF le target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L336-L337
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L336-L337

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

theorem Comp.HideOrRun.AF_le_target : (game.toCSG game_wf).AF ↑target ≤ (↑target : Set HR) := by sorry
