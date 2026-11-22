-- Prove2me | Theorems.Thm_CCS_pfx_isConf_insert
-- name    : CCS.pfx_isConf_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:58:10.788826+00:00
-- url     : https://prove2.me/theorems/26065cd5-f788-4122-8c79-3378884d23eb
-- title:
--   CCS: pfx is Conf insert
-- statement:
--   The CCS construction uses the pfx is Conf insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L376-L399
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L376-L399

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

theorem CCS.pfx_isConf_insert {c : Set (Option E.Event)} {x : E.Event}
    (hc : (pfx α E).toGES.isConf c) (hnone : none ∈ c)
    (hx : E.toGES.isConf ({z | some z ∈ c} ∪ {x})) (_hfr : some x ∉ c) :
    (pfx α E).toGES.isConf (c ∪ {some x}) := by sorry
