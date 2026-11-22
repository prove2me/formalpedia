-- Prove2me | Theorems.Thm_Csg_skirmish_run_not_mem_A_safe_hide
-- name    : Csg.skirmish_run_not_mem_A_safe_hide
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:18:18.145149+00:00
-- url     : https://prove2.me/theorems/07674b7a-de02-4d60-a24a-30ddca46b829
-- title:
--   Csg: skirmish run not mem A safe hide
-- statement:
--   **The payoff, the exclusion half of `skirmish_A_safe_hide_eq_singleton_hide`.** `run` is never
--       safe for `skirmishSafe` at `hide`, columns unexcused: `(run,throw) → wet ∉ skirmishSafe`. The
--       same argument already used inline inside Section 3b's `skirmish_hide_not_mem_Apre1_home_safe`,
--       extracted here as its own fact for reuse.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L628-L634
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L628-L634

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_run_not_mem_A_safe_hide :
    SoldierMove.run ∉ skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide := by sorry
