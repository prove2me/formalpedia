-- Prove2me | Theorems.Thm_Comp_HideOrRun_mid_le
-- name    : Comp.HideOrRun.mid_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:00:36.075379+00:00
-- url     : https://prove2.me/theorems/703c0b85-ad02-40e7-b07a-b6b59f96f318
-- title:
--   Hide Or Run: mid le
-- statement:
--   Every stage of the middle climb is a lower bound on the `μX` fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L209-L221
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L209-L221

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

theorem Comp.HideOrRun.mid_le (b y : Finset HR) (m : ℕ) :
    (↑((midStep b y)^[m] ∅) : Set HR) ≤ ((game.toCSG game_wf).LFInner ↑b ↑y).lfp := by sorry
