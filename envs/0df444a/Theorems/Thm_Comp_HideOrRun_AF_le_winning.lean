-- Prove2me | Theorems.Thm_Comp_HideOrRun_AF_le_winning
-- name    : Comp.HideOrRun.AF_le_winning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:02:00.510797+00:00
-- url     : https://prove2.me/theorems/e5f1eac5-b28b-4baf-b187-7838d5eb851c
-- title:
--   Hide Or Run: AF le winning
-- statement:
--   The Hide Or Run construction uses the AF le winning property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L323-L325
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L323-L325

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

theorem Comp.HideOrRun.AF_le_winning : (game.toCSG game_wf).AF ↑target ≤ (↑winning : Set HR) := by sorry
