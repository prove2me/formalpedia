-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_AGF_home
-- name    : Csg.skirmish_hide_not_mem_AGF_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:20:16.595545+00:00
-- url     : https://prove2.me/theorems/bbc67c80-325c-4906-98ff-b1c7cdafbfce
-- title:
--   Csg: skirmish hide not mem AGF home
-- statement:
--   **The headline false result.** `<<p1>> almost [ G F s=2 ]`: from `hide`, the soldier canNOT
--       force visiting `home` infinitely often almost surely -- the second half of the almost-vs-limit
--       Büchi divergence.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1330-L1333
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1330-L1333

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_AGF_home :
    SkirmishPos.hide ∉ skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
