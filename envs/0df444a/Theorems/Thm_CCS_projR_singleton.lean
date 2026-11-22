-- Prove2me | Theorems.Thm_CCS_projR_singleton
-- name    : CCS.projR_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:10:28.98097+00:00
-- url     : https://prove2.me/theorems/9f17fa41-6a2a-4da1-8538-f81b9e49df0d
-- title:
--   CCS: proj R singleton
-- statement:
--   The CCS construction uses the proj R singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L93-L97
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L93-L97

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projR_singleton (t : Tag E F) : projR {t} = {f | t.evR = some f} := by sorry
