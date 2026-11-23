-- Prove2me | Theorems.Thm_Csg_skirmish_Apre1_safe_top_subset
-- name    : Csg.skirmish_Apre1_safe_top_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:13.241099+00:00
-- url     : https://prove2.me/theorems/5b8866ee-f0de-4366-abf7-960b16b1a0d6
-- title:
--   Csg: skirmish Apre1 safe top subset
-- statement:
--   **The payoff.** One step down from `⊤`: `AFOuter {home} ⊤ ≤ skirmishSafe` -- `wet` is excluded
--       by `skirmish_wet_not_mem_Apre1` (`wet ∉ skirmishSafe`), and `hide`/`home` are trivially inside
--       `skirmishSafe` regardless of whether they are genuinely in `Apre1` or not. A single
--       `OrderHom.lfp_le` pre-fixed-point check against the candidate `skirmishSafe`, not an exact
--       computation of the inner `lfp`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L373-L379
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L373-L379

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_Apre1_safe_top_subset :
    skirmishCSG.Apre1 skirmishSafe (⊤ : Set SkirmishPos) ⊆ skirmishSafe := by sorry
