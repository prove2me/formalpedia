-- Prove2me | Theorems.Thm_Csg_skirmish_B_singleton_hide_safe_hide_eq_univ
-- name    : Csg.skirmish_B_singleton_hide_safe_hide_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:00:16.784128+00:00
-- url     : https://prove2.me/theorems/1b9fc0e9-1b2d-4e7c-a438-c9e22ab97b53
-- title:
--   Csg: skirmish B singleton hide safe hide eq univ
-- statement:
--   **The payoff.** Every sniper response escapes into `skirmishSafe` from `hide`, using the row
--       action `hide` alone: `wait` via `(hide,wait) → hide ∈ skirmishSafe`, `throw` via `(hide,throw)
--       → home ∈ skirmishSafe`. Simpler than Section 4a's analogous `{home}`-target computation, since
--       the broader target `skirmishSafe` (rather than the singleton `{home}`) needs no two-step
--       iteration -- `hide`'s own two outcomes already cover it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L668-L681
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L668-L681

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_B_singleton_hide_safe_hide_eq_univ :
    skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by sorry
