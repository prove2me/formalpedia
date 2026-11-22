-- Prove2me | Theorems.Thm_CCS_restrict_isConf_insert
-- name    : CCS.restrict_isConf_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:58:39.897985+00:00
-- url     : https://prove2.me/theorems/b4632fb4-d4e8-4f4e-ba36-9843af35e246
-- title:
--   CCS: restrict is Conf insert
-- statement:
--   The CCS construction uses the restrict is Conf insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L483-L512
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L483-L512

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

theorem CCS.restrict_isConf_insert {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    {x : E.Event} {hx : (E.label x).strip.isSome = true}
    (hc : (restrict E).toGES.isConf c)
    (hxc : E.toGES.isConf ({y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} ∪ {x})) :
    (restrict E).toGES.isConf (c ∪ {⟨x, hx⟩}) := by sorry
