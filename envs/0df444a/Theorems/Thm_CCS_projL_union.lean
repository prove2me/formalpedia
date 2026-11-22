-- Prove2me | Theorems.Thm_CCS_projL_union
-- name    : CCS.projL_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:09:49.630846+00:00
-- url     : https://prove2.me/theorems/487013ee-4c02-4130-bdf9-dd3273d6461f
-- title:
--   CCS: proj L union
-- statement:
--   The CCS construction uses the proj L union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L63-L71
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L63-L71

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_union (C D : Set (Tag E F)) : projL (C ∪ D) = projL C ∪ projL D := by sorry
