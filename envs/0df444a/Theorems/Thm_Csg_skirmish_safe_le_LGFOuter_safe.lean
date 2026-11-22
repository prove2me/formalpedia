-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LGFOuter_safe
-- name    : Csg.skirmish_safe_le_LGFOuter_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:26:49.703436+00:00
-- url     : https://prove2.me/theorems/2a841b19-9d4c-444e-9d7e-590acc254ee6
-- title:
--   Csg: skirmish safe le LGFOuter safe
-- statement:
--   **The payoff.** `skirmishSafe ≤ LGFOuter {home} skirmishSafe`, in exactly the two Kleene steps
--       up from `⊥` Section 4c's `skirmish_safe_le_LFOuter_safe` used for `LF` (`⊥ ↦ {home} ↦
--       skirmishSafe`, here re-derived one operator over for `LGFInner`) --
--       `OrderHom.map_map_bot_le_lfp` turning the two hand-checked steps into a genuine lower bound on
--       the inner `lfp`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1371-L1386
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1371-L1386

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LGFOuter_safe :
    skirmishSafe ≤ skirmishCSG.LGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by sorry
