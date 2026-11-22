-- Prove2me | Theorems.Thm_CCS_pfx_con
-- name    : CCS.pfx_con
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:57:06.020586+00:00
-- url     : https://prove2.me/theorems/2fdfafd2-7e6c-4fa1-bf56-31bb94216255
-- title:
--   CCS: pfx con
-- statement:
--   The CCS construction uses the pfx con property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L238-L246
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L238-L246

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

theorem CCS.pfx_con {c : Set (Option E.Event)} (h : (pfx α E).toGES.Consistent c) :
    E.toGES.Consistent {z | some z ∈ c} := by sorry
