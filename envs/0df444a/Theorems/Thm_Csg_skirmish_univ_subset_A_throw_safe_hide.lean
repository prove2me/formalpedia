-- Prove2me | Theorems.Thm_Csg_skirmish_univ_subset_A_throw_safe_hide
-- name    : Csg.skirmish_univ_subset_A_throw_safe_hide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:04.162563+00:00
-- url     : https://prove2.me/theorems/63d8c298-3aff-4364-9e45-2a79d1e555ec
-- title:
--   Csg: skirmish univ subset A throw safe hide
-- statement:
--   **The payoff.** Once `throw` is excused (already known escapable), *both* row actions become
--       safe for `skirmishSafe`: `hide` because `throw` is excused and `wait → hide ∈ skirmishSafe`;
--       `run` because `throw` is excused and `wait → home ∈ skirmishSafe`. The second real step of the
--       inner `LW` computation, reaching `Set.univ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L492-L512
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L492-L512

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_univ_subset_A_throw_safe_hide :
    (Set.univ : Set SoldierMove) ⊆
      skirmishCSG.A ({SniperMove.throw} : Set SniperMove) skirmishSafe SkirmishPos.hide := by sorry
