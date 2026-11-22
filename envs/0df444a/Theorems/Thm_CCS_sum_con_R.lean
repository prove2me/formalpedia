-- Prove2me | Theorems.Thm_CCS_sum_con_R
-- name    : CCS.sum_con_R
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:57:34.632355+00:00
-- url     : https://prove2.me/theorems/b7c560c4-a0df-4087-bd5c-d5f3a754e991
-- title:
--   CCS: sum con R
-- statement:
--   The CCS construction uses the sum con R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L277-L286
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L277-L286

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

theorem CCS.sum_con_R {c : Set (E.Event ⊕ F.Event)} (h : (sum E F).toGES.Consistent c) :
    F.toGES.Consistent {z | Sum.inr z ∈ c} := by sorry
