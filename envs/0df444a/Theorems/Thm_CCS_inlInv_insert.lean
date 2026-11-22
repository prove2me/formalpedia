-- Prove2me | Theorems.Thm_CCS_inlInv_insert
-- name    : CCS.inlInv_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:14.290549+00:00
-- url     : https://prove2.me/theorems/05db8f86-5e2e-444b-b70b-563d659e4b71
-- title:
--   CCS: inl Inv insert
-- statement:
--   The CCS construction uses the inl Inv insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L401-L410
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L401-L410

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

theorem CCS.inlInv_insert {c : Set (E.Event ⊕ F.Event)} {x : E.Event} :
    {z | Sum.inl z ∈ c ∪ ({Sum.inl x} : Set (E.Event ⊕ F.Event))} = {z | Sum.inl z ∈ c} ∪ {x} := by sorry
