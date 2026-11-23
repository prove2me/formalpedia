-- Prove2me | Theorems.Thm_Csg_skirmish_A_empty_safe_le_LFV_empty_safe_safe
-- name    : Csg.skirmish_A_empty_safe_le_LFV_empty_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:06:16.119707+00:00
-- url     : https://prove2.me/theorems/032ffca3-dfaf-4678-9a13-00f59c342b9d
-- title:
--   Csg: skirmish A empty safe le LFV empty safe safe
-- statement:
--   **The payoff.** Since `LFVStep ∅ safe safe s` is `V ↦ LFW V ∅ safe safe s`, and the latter is
--       the *same* constant `A ∅ safe s` regardless of `V` (`skirmish_LFW_empty_safe_safe`), that
--       constant is trivially a post-fixed point of `LFVStep ∅ safe safe s` at itself -- `OrderHom.
--       le_gfp` turns this into a lower bound on the actual `LFV`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L958-L966
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L958-L966

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_A_empty_safe_le_LFV_empty_safe_safe (s : SkirmishPos) :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe s ≤
      skirmishCSG.LFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe s := by sorry
