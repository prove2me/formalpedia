-- Prove2me | Theorems.Thm_CCS_projR_insert_none
-- name    : CCS.projR_insert_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:36.033794+00:00
-- url     : https://prove2.me/theorems/99abd5ff-244a-46ca-85b6-36992604cb30
-- title:
--   CCS: proj R insert none
-- statement:
--   The CCS construction uses the proj R insert none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L334-L345
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L334-L345

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

theorem CCS.projR_insert_none {t : Tag E F} (hy : t.evR = none) :
    projR (c ∪ {t}) = projR c := by sorry
