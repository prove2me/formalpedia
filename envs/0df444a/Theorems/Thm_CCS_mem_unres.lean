-- Prove2me | Theorems.Thm_CCS_mem_unres
-- name    : CCS.mem_unres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:28.401924+00:00
-- url     : https://prove2.me/theorems/e195139b-22c2-47ed-8d42-3a311a0f3cec
-- title:
--   CCS: mem unres
-- statement:
--   The CCS construction uses the mem unres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L520-L524
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L520-L524

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
variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}

theorem CCS.mem_unres {x : E.Event} (hx : (E.label x).strip.isSome = true) :
    x ∈ unres c ↔ (⟨x, hx⟩ : (restrict E).Event) ∈ c := by sorry
