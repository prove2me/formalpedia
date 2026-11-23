-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFpre1_empty_safe_safe
-- name    : Csg.skirmish_hide_mem_AFpre1_empty_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:19:55.594564+00:00
-- url     : https://prove2.me/theorems/b6cf29a1-27e1-4382-90df-9f3d30f9aecf
-- title:
--   Csg: skirmish hide mem AFpre1 empty safe safe
-- statement:
--   The Csg construction uses the skirmish hide mem AFpre1 empty safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L813-L815
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L813-L815

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFpre1_empty_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by sorry
