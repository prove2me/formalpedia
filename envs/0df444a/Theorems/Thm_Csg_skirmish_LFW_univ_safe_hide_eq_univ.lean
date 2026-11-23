-- Prove2me | Theorems.Thm_Csg_skirmish_LFW_univ_safe_hide_eq_univ
-- name    : Csg.skirmish_LFW_univ_safe_hide_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:23:12.993561+00:00
-- url     : https://prove2.me/theorems/cbfcd939-2785-434b-8a59-ebf726e1db6f
-- title:
--   Csg: skirmish LFW univ safe hide eq univ
-- statement:
--   **The payoff.** At `x := skirmishSafe`, picking the outer witness `v := Set.univ` makes the
--       second (constant) factor of `LFWStep` reduce to `Set.univ` outright
--       (`skirmish_B_univ_safe_hide_eq_univ` feeding `CSG.A_univ_v2`), so the whole map reduces to
--       `LStep safe safe hide` alone (`Set.inter_univ`) -- the *same* map Section 4b's `LW` already
--       Kleene-iterated, converging in the *same* two steps: `∅ ↦ {hide} ↦ Set.univ`.
--       `OrderHom.map_map_bot_le_lfp` turns this into a genuine lower bound on `LFW`'s own `μW` fixed
--       point, pinning it to `Set.univ` exactly since `Set.univ` is already the top.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1018-L1055
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1018-L1055

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_LFW_univ_safe_hide_eq_univ :
    skirmishCSG.LFW (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.hide
      = (Set.univ : Set SoldierMove) := by sorry
