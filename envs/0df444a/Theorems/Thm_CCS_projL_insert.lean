-- Prove2me | Theorems.Thm_CCS_projL_insert
-- name    : CCS.projL_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:05.25581+00:00
-- url     : https://prove2.me/theorems/8b62432d-2361-4321-af7c-17fb6d904b46
-- title:
--   CCS: proj L insert
-- statement:
--   The CCS construction uses the proj L insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L291-L304
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L291-L304

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

theorem CCS.projL_insert {t : Tag E F} {x : E.Event} (hx : t.evL = some x) :
    projL (c ∪ {t}) = projL c ∪ {x} := by sorry
