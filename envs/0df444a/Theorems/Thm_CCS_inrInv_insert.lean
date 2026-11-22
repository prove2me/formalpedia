-- Prove2me | Theorems.Thm_CCS_inrInv_insert
-- name    : CCS.inrInv_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:19.091686+00:00
-- url     : https://prove2.me/theorems/6013203b-03a3-459b-85b1-493025c93758
-- title:
--   CCS: inr Inv insert
-- statement:
--   The CCS construction uses the inr Inv insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L412-L421
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L412-L421

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

theorem CCS.inrInv_insert {c : Set (E.Event ⊕ F.Event)} {y : F.Event} :
    {z | Sum.inr z ∈ c ∪ ({Sum.inr y} : Set (E.Event ⊕ F.Event))} = {z | Sum.inr z ∈ c} ∪ {y} := by sorry
