-- Prove2me | Theorems.Thm_CCS_pmapSet_unres
-- name    : CCS.pmapSet_unres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:57.661563+00:00
-- url     : https://prove2.me/theorems/b2cbe00f-8925-4c89-bd9a-c90aeb50f554
-- title:
--   CCS: pmap Set unres
-- statement:
--   The CCS construction uses the pmap Set unres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L337-L346
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L337-L346

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

theorem CCS.pmapSet_unres {E : SES (Action (Option Name))} (s : Set (restrict E).Event) :
    GES.pmapSet (G := (restrict E).toGES) (H := E.toGES) (fun e => some e.1) s
      = {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ s} := by sorry
