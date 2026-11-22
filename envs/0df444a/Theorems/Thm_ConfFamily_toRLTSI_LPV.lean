-- Prove2me | Theorems.Thm_ConfFamily_toRLTSI_LPV
-- name    : ConfFamily.toRLTSI_LPV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:40:31.753805+00:00
-- url     : https://prove2.me/theorems/0afa6339-5d87-417d-bbbb-b5a86c98df08
-- title:
--   Conf Family: to RLTSI LPV
-- statement:
--   The reversible LTSI of a stable family satisfies the reverse LPV axioms.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L95-L155
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L95-L155

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem ConfFamily.toRLTSI_LPV (hF : Stable F) : RLTSI.LPV (toRLTSI F) := by sorry
