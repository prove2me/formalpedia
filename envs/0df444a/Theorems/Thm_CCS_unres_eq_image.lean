-- Prove2me | Theorems.Thm_CCS_unres_eq_image
-- name    : CCS.unres_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:58:49.66212+00:00
-- url     : https://prove2.me/theorems/7875a7e2-c654-4ebd-9dc1-52aab027444b
-- title:
--   CCS: unres eq image
-- statement:
--   The CCS construction uses the unres eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L526-L530
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L526-L530

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
variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}

theorem CCS.unres_eq_image : unres c = Subtype.val '' c := by sorry
