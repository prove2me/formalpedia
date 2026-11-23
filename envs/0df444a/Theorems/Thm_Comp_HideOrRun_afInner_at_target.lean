-- Prove2me | Theorems.Thm_Comp_HideOrRun_afInner_at_target
-- name    : Comp.HideOrRun.afInner_at_target
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:03:21.89779+00:00
-- url     : https://prove2.me/theorems/a2a6693a-3581-43da-bdad-3ea2f073cb87
-- title:
--   Hide Or Run: af Inner at target
-- statement:
--   And the outer chain has stopped.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L340-L343
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L340-L343

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

theorem Comp.HideOrRun.afInner_at_target :
    ((game.toCSG game_wf).AFInner ↑target ↑target).lfp = (↑target : Set HR) := by sorry
