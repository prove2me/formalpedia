-- Prove2me | Theorems.Thm_CCS_pmapSet_inl
-- name    : CCS.pmapSet_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:56.029837+00:00
-- url     : https://prove2.me/theorems/ca826f1c-e4f2-4c9c-ba90-6732f33c3a59
-- title:
--   CCS: pmap Set inl
-- statement:
--   The CCS construction uses the pmap Set inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L220-L227
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L220-L227

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

theorem CCS.pmapSet_inl (s : Set (E.Event ⊕ F.Event)) :
    GES.pmapSet (G := (sum E F).toGES) (H := E.toGES) Sum.getLeft? s
      = {z | Sum.inl z ∈ s} := by sorry
