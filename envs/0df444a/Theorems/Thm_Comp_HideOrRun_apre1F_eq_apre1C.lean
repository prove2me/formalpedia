-- Prove2me | Theorems.Thm_Comp_HideOrRun_apre1F_eq_apre1C
-- name    : Comp.HideOrRun.apre1F_eq_apre1C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:19.478803+00:00
-- url     : https://prove2.me/theorems/a69d34ac-6619-40e7-8075-e6642e88fc5f
-- title:
--   Hide Or Run: apre1 F eq apre1 C
-- statement:
--   The Hide Or Run construction uses the apre1 F eq apre1 C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L297-L300
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L297-L300

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

theorem Comp.HideOrRun.apre1F_eq_apre1C (x y : Finset HR) : game.apre1F x y = apre1C x y := by sorry
