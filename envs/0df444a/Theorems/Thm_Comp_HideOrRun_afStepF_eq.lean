-- Prove2me | Theorems.Thm_Comp_HideOrRun_afStepF_eq
-- name    : Comp.HideOrRun.afStepF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:50:19.507476+00:00
-- url     : https://prove2.me/theorems/9eeec387-e0a0-453c-8cfa-67b652790066
-- title:
--   Hide Or Run: af Step F eq
-- statement:
--   The Hide Or Run construction uses the af Step F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L305-L308
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L305-L308

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

theorem Comp.HideOrRun.afStepF_eq (b y : Finset HR) : game.afStepF b y = afStepC b y := by sorry
