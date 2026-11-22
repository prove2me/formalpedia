-- Prove2me | Theorems.Thm_CCS_pfx_isConf
-- name    : CCS.pfx_isConf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:54:48.344902+00:00
-- url     : https://prove2.me/theorems/d742996b-8d81-49e8-9e8a-ff5fa7195162
-- title:
--   CCS: pfx is Conf
-- statement:
--   The `E`-part of a configuration of `α.E` is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L249-L258
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L249-L258

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

theorem CCS.pfx_isConf {c : Set (Option E.Event)}
    (hc : (pfx α E).toGES.isConf c) : E.toGES.isConf {z | some z ∈ c} := by sorry
