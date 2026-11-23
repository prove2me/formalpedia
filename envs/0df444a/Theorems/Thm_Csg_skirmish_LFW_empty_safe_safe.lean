-- Prove2me | Theorems.Thm_Csg_skirmish_LFW_empty_safe_safe
-- name    : Csg.skirmish_LFW_empty_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:21:35.541625+00:00
-- url     : https://prove2.me/theorems/085bfd1e-8e9a-48b1-9abd-2891f371db97
-- title:
--   Csg: skirmish LFW empty safe safe
-- statement:
--   **The payoff.** With the escape target `x` set to `∅`, *both* of `LFWStep`'s `B` calls
--       collapse via `CSG.B_empty_x` regardless of their row-action argument (the inner `W` and the
--       outer witness `v` alike), leaving the same constant `A ∅ safe s` on both sides of the
--       intersection (`Set.inter_self`) -- so `LFW`'s own `μW` fixed point is exactly that constant,
--       for *any* outer witness `v`. The `LFpre1`-level mirror of Section 5e's `AFVStep`-at-`x:=∅`
--       collapse, one layer further in.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L929-L950
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L929-L950

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_LFW_empty_safe_safe (v : Set SoldierMove) (s : SkirmishPos) :
    skirmishCSG.LFW v (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s
      = skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s := by sorry
