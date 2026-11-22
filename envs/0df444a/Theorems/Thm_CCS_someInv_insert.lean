-- Prove2me | Theorems.Thm_CCS_someInv_insert
-- name    : CCS.someInv_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:25.567347+00:00
-- url     : https://prove2.me/theorems/e6156f6f-dc35-49f2-a3b0-bfe51bcb1572
-- title:
--   CCS: some Inv insert
-- statement:
--   The CCS construction uses the some Inv insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L365-L374
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L365-L374

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

theorem CCS.someInv_insert {c : Set (Option E.Event)} {x : E.Event} :
    {z | some z ∈ c ∪ ({some x} : Set (Option E.Event))} = {z | some z ∈ c} ∪ {x} := by sorry
