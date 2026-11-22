-- Prove2me | Theorems.Thm_CCS_projR_empty
-- name    : CCS.projR_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:10:19.886649+00:00
-- url     : https://prove2.me/theorems/b302fce6-22e4-4a28-910f-643c4fa17b82
-- title:
--   CCS: proj R empty
-- statement:
--   The CCS construction uses the proj R empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L85-L85
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L85-L85

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projR_empty : projR (∅ : Set (Tag E F)) = ∅ := by sorry
