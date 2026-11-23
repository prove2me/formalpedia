-- Prove2me | Theorems.Thm_Csg_skirmish_A_safe_hide_eq_singleton_hide
-- name    : Csg.skirmish_A_safe_hide_eq_singleton_hide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:00:22.48446+00:00
-- url     : https://prove2.me/theorems/20653402-7b67-44ee-98d9-45d1d257e2a5
-- title:
--   Csg: skirmish A safe hide eq singleton hide
-- statement:
--   **The payoff.** `A ∅ safe hide` is not merely nonempty -- it is *exactly* `{hide}`: `⊇` from
--       the already-proven `skirmish_hide_mem_A_safe_hide` (Section 4a); `⊆` from
--       `skirmish_run_not_mem_A_safe_hide` (`SoldierMove` has only two constructors, so failing `run`
--       leaves only `hide`). The exact value the `AFVStep` fixed-point check below needs -- an
--       inclusion alone would not pin `AFVStep`'s image down to `{hide}` on the nose.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L641-L648
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L641-L648

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_A_safe_hide_eq_singleton_hide :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.hide = {SoldierMove.hide} := by sorry
