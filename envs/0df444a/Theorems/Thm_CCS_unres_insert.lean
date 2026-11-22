-- Prove2me | Theorems.Thm_CCS_unres_insert
-- name    : CCS.unres_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:33.944623+00:00
-- url     : https://prove2.me/theorems/50ee132b-3ea0-4f75-8bfd-cd2f64d4bb5f
-- title:
--   CCS: unres insert
-- statement:
--   The CCS construction uses the unres insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L535-L544
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L535-L544

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

theorem CCS.unres_insert {x : E.Event} (hx : (E.label x).strip.isSome = true) :
    unres (c ∪ {⟨x, hx⟩}) = unres c ∪ {x} := by sorry
