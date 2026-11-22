-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_A_safe_hide
-- name    : Csg.skirmish_hide_mem_A_safe_hide
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:00:10.037732+00:00
-- url     : https://prove2.me/theorems/d8f9ae4c-39e5-4830-ae8d-4ef189749cec
-- title:
--   Csg: skirmish hide mem A safe hide
-- statement:
--   **The payoff.** `hide` is unconditionally safe for `skirmishSafe`, with *no* column actions
--       excused: both of `hide`'s own responses (`(hide,wait) → hide`, `(hide,throw) → home`) already
--       land in `skirmishSafe`. The base case (`v2 = ∅`) the inner `LW` computation starts from.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L466-L477
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L466-L477

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_A_safe_hide :
    SoldierMove.hide ∈ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by sorry
