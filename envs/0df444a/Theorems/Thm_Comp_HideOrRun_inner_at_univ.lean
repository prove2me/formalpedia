-- Prove2me | Theorems.Thm_Comp_HideOrRun_inner_at_univ
-- name    : Comp.HideOrRun.inner_at_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:00:40.425214+00:00
-- url     : https://prove2.me/theorems/db603cff-fee9-4ba9-b88c-cc33ccd86755
-- title:
--   Hide Or Run: inner at univ
-- statement:
--   The first outer step: the `μX` fixed point at `Finset.univ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L264-L267
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L264-L267

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

theorem Comp.HideOrRun.inner_at_univ :
    ((game.toCSG game_wf).LFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) := by sorry
