-- Prove2me | Theorems.Thm_Comp_HideOrRun_lw_fixed
-- name    : Comp.HideOrRun.lw_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:59:59.664046+00:00
-- url     : https://prove2.me/theorems/86f8febc-d2c5-4959-a17f-aa415cfeb592
-- title:
--   Hide Or Run: lw fixed
-- statement:
--   Two steps really do suffice, for every pair of regions and every state: eight times eight
--       times three instances, checked outright. This is what turns `hr_LW` into a general lemma and so
--       makes `midStep` a function of `x` alone.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L178-L179
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L178-L179

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

theorem Comp.HideOrRun.lw_fixed : ∀ (x y : Finset HR) (s : HR), lStepC x y s (lwC x y s) = lwC x y s := by sorry
