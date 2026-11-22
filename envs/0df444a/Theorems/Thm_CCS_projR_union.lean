-- Prove2me | Theorems.Thm_CCS_projR_union
-- name    : CCS.projR_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:09:44.731334+00:00
-- url     : https://prove2.me/theorems/35f1278e-03a0-4656-b999-17b62466ed3c
-- title:
--   CCS: proj R union
-- statement:
--   The CCS construction uses the proj R union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L73-L81
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L73-L81

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projR_union (C D : Set (Tag E F)) : projR (C ∪ D) = projR C ∪ projR D := by sorry
