-- Prove2me | Theorems.Thm_ConfFamily_toLTSI_LPV
-- name    : ConfFamily.toLTSI_LPV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:38:18.04575+00:00
-- url     : https://prove2.me/theorems/ae696123-55ef-4d5b-ab0f-77259db002e5
-- title:
--   Conf Family: to LTSI LPV
-- statement:
--   The forward LPV axioms hold for every configuration family.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/LTSI.lean#L34-L68
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/LTSI.lean#L34-L68

import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Family_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily

theorem ConfFamily.toLTSI_LPV : LTSI.LPV (toLTSI F) := by sorry
