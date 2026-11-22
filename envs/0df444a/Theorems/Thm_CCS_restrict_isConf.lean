-- Prove2me | Theorems.Thm_CCS_restrict_isConf
-- name    : CCS.restrict_isConf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:55:14.939802+00:00
-- url     : https://prove2.me/theorems/d9d1ac94-c311-4e74-a6c6-9905f0ff7b21
-- title:
--   CCS: restrict is Conf
-- statement:
--   The `E`-part of a configuration of `(ν)E` is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L349-L361
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L349-L361

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

theorem CCS.restrict_isConf {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    (hc : (restrict E).toGES.isConf c) :
    E.toGES.isConf {y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} := by sorry
