-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_AFGInner_safe_safe_safe
-- name    : Csg.skirmish_safe_le_AFGInner_safe_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:20:42.152506+00:00
-- url     : https://prove2.me/theorems/bfd8d031-d060-4c39-9619-3b477bd7826a
-- title:
--   Csg: skirmish safe le AFGInner safe safe safe
-- statement:
--   **The payoff.** `skirmishSafe` is a post-fixed point of `AFGInner safe safe safe`, at `y =
--       safe`: every `s ∈ safe` takes the `b`-branch (`AFpre1 safe safe safe ∩ safe`), since it is
--       already in both conjuncts (`skirmish_safe_subset_AFpre1_safe_safe_safe`, and `hs` itself).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L834-L839
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L834-L839

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_AFGInner_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGInner skirmishSafe skirmishSafe skirmishSafe skirmishSafe := by sorry
