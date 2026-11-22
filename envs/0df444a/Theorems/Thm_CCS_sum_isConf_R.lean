-- Prove2me | Theorems.Thm_CCS_sum_isConf_R
-- name    : CCS.sum_isConf_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:08.757406+00:00
-- url     : https://prove2.me/theorems/d309dc84-faa0-4a82-ab47-3c7f00baedcb
-- title:
--   CCS: sum is Conf R
-- statement:
--   The `F`-part of a configuration of `E + F` is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L300-L308
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L300-L308

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

theorem CCS.sum_isConf_R {c : Set (E.Event ⊕ F.Event)}
    (hc : (sum E F).toGES.isConf c) : F.toGES.isConf {z | Sum.inr z ∈ c} := by sorry
