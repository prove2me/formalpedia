-- Prove2me | Theorems.Thm_Csg_skirmish_safe_subset_LFpre1_safe_safe_safe
-- name    : Csg.skirmish_safe_subset_LFpre1_safe_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:23:55.133463+00:00
-- url     : https://prove2.me/theorems/72a56bd3-d4ad-4596-8d0b-bae9c16ca71e
-- title:
--   Csg: skirmish safe subset LFpre1 safe safe safe
-- statement:
--   The Csg construction uses the skirmish safe subset LFpre1 safe safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1129-L1135
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1129-L1135

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_subset_LFpre1_safe_safe_safe :
    skirmishSafe ⊆ skirmishCSG.LFpre1 skirmishSafe skirmishSafe skirmishSafe := by sorry
