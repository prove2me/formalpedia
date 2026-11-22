-- Prove2me | Theorems.Thm_CCS_restrict_con
-- name    : CCS.restrict_con
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:57:46.807328+00:00
-- url     : https://prove2.me/theorems/fce48416-e49e-4bdc-b73a-fb2b107f48ab
-- title:
--   CCS: restrict con
-- statement:
--   The CCS construction uses the restrict con property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L321-L335
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L321-L335

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

theorem CCS.restrict_con {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (h : (restrict E).toGES.Consistent c) :
    E.toGES.Consistent {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by sorry
