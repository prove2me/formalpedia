-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LFGInner_safe_safe_safe
-- name    : Csg.skirmish_safe_le_LFGInner_safe_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:23:58.696441+00:00
-- url     : https://prove2.me/theorems/ef44b483-1729-4a29-8c55-11deb8c31b5d
-- title:
--   Csg: skirmish safe le LFGInner safe safe safe
-- statement:
--   The Csg construction uses the skirmish safe le LFGInner safe safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1139-L1144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1139-L1144

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LFGInner_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.LFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by sorry
