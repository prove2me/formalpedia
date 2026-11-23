-- Prove2me | Theorems.Thm_Comp_HideOrRun_aF_eq_aC
-- name    : Comp.HideOrRun.aF_eq_aC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:50:51.374932+00:00
-- url     : https://prove2.me/theorems/3f4152c8-9fbb-4686-b02a-0f108e57dccd
-- title:
--   Hide Or Run: a F eq a C
-- statement:
--   The Hide Or Run construction uses the a F eq a C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L150-L152
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L150-L152

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

theorem Comp.HideOrRun.aF_eq_aC (v2 : Finset Bool) (y : Finset HR) (s : HR) : game.aF v2 y s = aC v2 y s := by sorry
