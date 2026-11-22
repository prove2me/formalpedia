-- Prove2me | Theorems.Thm_CCS_projL_insert_none
-- name    : CCS.projL_insert_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:41.496941+00:00
-- url     : https://prove2.me/theorems/1c5bb4be-9225-4ac9-8e83-30af0d7ebdef
-- title:
--   CCS: proj L insert none
-- statement:
--   The CCS construction uses the proj L insert none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L306-L317
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L306-L317

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}

theorem CCS.projL_insert_none {t : Tag E F} (hx : t.evL = none) :
    projL (c ∪ {t}) = projL c := by sorry
