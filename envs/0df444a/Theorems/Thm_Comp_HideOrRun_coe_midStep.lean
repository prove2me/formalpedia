-- Prove2me | Theorems.Thm_Comp_HideOrRun_coe_midStep
-- name    : Comp.HideOrRun.coe_midStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:28.705053+00:00
-- url     : https://prove2.me/theorems/96cd9ff4-6cbf-498d-8a0e-581f413ce3fb
-- title:
--   Hide Or Run: coe mid Step
-- statement:
--   The Hide Or Run construction uses the coe mid Step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L202-L206
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L202-L206

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

theorem Comp.HideOrRun.coe_midStep (b y x : Finset HR) :
    (game.toCSG game_wf).LFInner ↑b ↑y ↑x = (↑(midStep b y x) : Set HR) := by sorry
