-- Prove2me | Theorems.Thm_CCS_projL_singleton
-- name    : CCS.projL_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:10:27.740427+00:00
-- url     : https://prove2.me/theorems/a64c7764-c8b1-4d48-9d57-5917cfc58fdd
-- title:
--   CCS: proj L singleton
-- statement:
--   The CCS construction uses the proj L singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L87-L91
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L87-L91

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_singleton (t : Tag E F) : projL {t} = {e | t.evL = some e} := by sorry
