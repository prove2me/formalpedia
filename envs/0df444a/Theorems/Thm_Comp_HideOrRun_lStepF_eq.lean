-- Prove2me | Theorems.Thm_Comp_HideOrRun_lStepF_eq
-- name    : Comp.HideOrRun.lStepF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:59:55.484691+00:00
-- url     : https://prove2.me/theorems/27954b47-1dbe-499f-84f9-782552d3edce
-- title:
--   Hide Or Run: l Step F eq
-- statement:
--   The Hide Or Run construction uses the l Step F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L165-L168
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L165-L168

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

theorem Comp.HideOrRun.lStepF_eq (x y : Finset HR) (s : HR) : game.lStepF x y s = lStepC x y s := by sorry
