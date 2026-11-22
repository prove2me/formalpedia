-- Prove2me | Theorems.Thm_CCS_pfx_none_mem
-- name    : CCS.pfx_none_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:52.765672+00:00
-- url     : https://prove2.me/theorems/4b5a948b-121c-4ed3-aebb-04cd6e42373b
-- title:
--   CCS: pfx none mem
-- statement:
--   Every other event of a configuration of `α.E` requires the prefix.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L261-L264
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L261-L264

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

theorem CCS.pfx_none_mem {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) {z : E.Event} (hz : some z ∈ c) : none ∈ c := by sorry
