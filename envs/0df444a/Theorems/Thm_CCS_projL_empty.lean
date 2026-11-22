-- Prove2me | Theorems.Thm_CCS_projL_empty
-- name    : CCS.projL_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:10:05.146193+00:00
-- url     : https://prove2.me/theorems/bc4ca9aa-2935-4f48-abb0-5504aa67a150
-- title:
--   CCS: proj L empty
-- statement:
--   The CCS construction uses the proj L empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L83-L83
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L83-L83

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}

theorem CCS.projL_empty : projL (∅ : Set (Tag E F)) = ∅ := by sorry
