-- Prove2me | Theorems.Thm_Comp_HideOrRun_dirac_ne_zero_iff
-- name    : Comp.HideOrRun.dirac_ne_zero_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:59:38.548952+00:00
-- url     : https://prove2.me/theorems/7c4d62f5-8a35-48de-ba65-eed21b2d33f5
-- title:
--   Hide Or Run: dirac ne zero iff
-- statement:
--   The Hide Or Run construction uses the dirac ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L95-L99
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L95-L99

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

theorem Comp.HideOrRun.dirac_ne_zero_iff (t s' : HR) : dirac t s' ≠ 0 ↔ s' = t := by sorry
