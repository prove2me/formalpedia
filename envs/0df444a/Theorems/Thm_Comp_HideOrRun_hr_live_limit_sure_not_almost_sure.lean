-- Prove2me | Theorems.Thm_Comp_HideOrRun_hr_live_limit_sure_not_almost_sure
-- name    : Comp.HideOrRun.hr_live_limit_sure_not_almost_sure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:45:26.436696+00:00
-- url     : https://prove2.me/theorems/30609973-0fbd-4b57-8620-e783c8140159
-- title:
--   Hide Or Run: hr live limit sure not almost sure
-- statement:
--   **The separation, as a theorem.** `live` is a value-1 state for reaching `goal` from which no
--       strategy wins almost surely -- the gap that makes `LF`, and not `AF`, the operator a
--       probabilistic reachability precomputation has to use.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L352-L359
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L352-L359

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

theorem Comp.HideOrRun.hr_live_limit_sure_not_almost_sure :
    HR.live ∈ (game.toCSG game_wf).LF ↑target ∧
      HR.live ∉ (game.toCSG game_wf).AF ↑target := by sorry
