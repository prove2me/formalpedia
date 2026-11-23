-- Prove2me | Theorems.Thm_Csg_skirmish_AFVStep_empty_safe_safe_hide_fixed
-- name    : Csg.skirmish_AFVStep_empty_safe_safe_hide_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:19:32.569851+00:00
-- url     : https://prove2.me/theorems/c5fa78ae-92f3-4c83-9ecc-c5ef43f5b5fe
-- title:
--   Csg: skirmish AFVStep empty safe safe hide fixed
-- statement:
--   **The payoff.** With the escape target `x` set to `∅`, `AFVStep`'s second factor collapses to
--       a *constant* (`CSG.B_empty_x`: `B V ∅ s = ∅` for *any* row-action pool `V`), so the whole map
--       no longer depends on its input `V` at all -- `{hide}` (in fact, *every* `V`) is trivially an
--       exact fixed point at `hide`, since both factors reduce to the same constant
--       `A ∅ safe hide = {hide}` (`Set.inter_self`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L775-L785
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L775-L785

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFVStep_empty_safe_safe_hide_fixed :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by sorry
