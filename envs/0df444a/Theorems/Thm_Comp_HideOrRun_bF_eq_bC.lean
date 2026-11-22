-- Prove2me | Theorems.Thm_Comp_HideOrRun_bF_eq_bC
-- name    : Comp.HideOrRun.bF_eq_bC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:49:01.349141+00:00
-- url     : https://prove2.me/theorems/4e8eb2cf-cd44-4cae-84a4-a3b5d1bfe4a6
-- title:
--   Hide Or Run: b F eq b C
-- statement:
--   The Hide Or Run construction uses the b F eq b C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L158-L160
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L158-L160

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

theorem Comp.HideOrRun.bF_eq_bC (v1 : Finset Bool) (x : Finset HR) (s : HR) : game.bF v1 x s = bC v1 x s := by sorry
