-- Prove2me | Theorems.Thm_CCS_sum_not_mixed
-- name    : CCS.sum_not_mixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:54.553979+00:00
-- url     : https://prove2.me/theorems/f9dd9049-ad65-4c09-a261-d72f544a62ad
-- title:
--   CCS: sum not mixed
-- statement:
--   A configuration of `E + F` never mixes the two sides.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L311-L319
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L311-L319

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}

theorem CCS.sum_not_mixed {c : Set (E.Event ⊕ F.Event)} (hc : (sum E F).toGES.isConf c)
    {z : E.Event} (hz : Sum.inl z ∈ c) {w : F.Event} (hw : Sum.inr w ∈ c) : False := by sorry
