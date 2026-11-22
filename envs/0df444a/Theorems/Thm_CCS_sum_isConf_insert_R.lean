-- Prove2me | Theorems.Thm_CCS_sum_isConf_insert_R
-- name    : CCS.sum_isConf_insert_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:58:28.451676+00:00
-- url     : https://prove2.me/theorems/4c0cd2fc-6904-4ca4-89c1-6f50e0c2d795
-- title:
--   CCS: sum is Conf insert R
-- statement:
--   The CCS construction uses the sum is Conf insert R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L453-L481
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L453-L481

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

theorem CCS.sum_isConf_insert_R {c : Set (E.Event ⊕ F.Event)} {y : F.Event}
    (hc : (sum E F).toGES.isConf c) (hnoL : ¬ ∃ e, Sum.inl e ∈ c)
    (hy : F.toGES.isConf ({z | Sum.inr z ∈ c} ∪ {y})) :
    (sum E F).toGES.isConf (c ∪ {Sum.inr y}) := by sorry
