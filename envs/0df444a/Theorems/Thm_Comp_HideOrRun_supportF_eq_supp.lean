-- Prove2me | Theorems.Thm_Comp_HideOrRun_supportF_eq_supp
-- name    : Comp.HideOrRun.supportF_eq_supp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:50:35.168744+00:00
-- url     : https://prove2.me/theorems/13d0e5b5-8766-436a-9a1c-df104d531079
-- title:
--   Hide Or Run: support F eq supp
-- statement:
--   **The quarantine.** Past this lemma there is no `ℚ` in the file.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L137-L142
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L137-L142

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

theorem Comp.HideOrRun.supportF_eq_supp (s : HR) (a1 a2 : Bool) : game.supportF s a1 a2 = supp s a1 a2 := by sorry
