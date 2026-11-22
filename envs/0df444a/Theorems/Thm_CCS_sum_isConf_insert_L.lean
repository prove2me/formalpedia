-- Prove2me | Theorems.Thm_CCS_sum_isConf_insert_L
-- name    : CCS.sum_isConf_insert_L
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:58:21.075155+00:00
-- url     : https://prove2.me/theorems/7edf1f36-00bb-4007-9d3b-969510f2baa3
-- title:
--   CCS: sum is Conf insert L
-- statement:
--   The CCS construction uses the sum is Conf insert L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L423-L451
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L423-L451

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

theorem CCS.sum_isConf_insert_L {c : Set (E.Event ⊕ F.Event)} {x : E.Event}
    (hc : (sum E F).toGES.isConf c) (hnoR : ¬ ∃ f, Sum.inr f ∈ c)
    (hx : E.toGES.isConf ({z | Sum.inl z ∈ c} ∪ {x})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inl x}) := by sorry
