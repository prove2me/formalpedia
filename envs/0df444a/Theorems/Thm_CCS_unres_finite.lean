-- Prove2me | Theorems.Thm_CCS_unres_finite
-- name    : CCS.unres_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:11:20.461935+00:00
-- url     : https://prove2.me/theorems/6374f6ef-49db-4080-abe0-b52173a881cf
-- title:
--   CCS: unres finite
-- statement:
--   The CCS construction uses the unres finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L532-L533
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L532-L533

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

theorem CCS.unres_finite (h : c.Finite) : (unres c).Finite := by sorry
