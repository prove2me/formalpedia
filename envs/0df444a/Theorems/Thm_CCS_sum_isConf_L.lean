-- Prove2me | Theorems.Thm_CCS_sum_isConf_L
-- name    : CCS.sum_isConf_L
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:53:52.901652+00:00
-- url     : https://prove2.me/theorems/79ca4a43-ca22-456a-96a3-4cc2f0c2ae45
-- title:
--   CCS: sum is Conf L
-- statement:
--   The `E`-part of a configuration of `E + F` is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L289-L297
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean#L289-L297

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

theorem CCS.sum_isConf_L {c : Set (E.Event ⊕ F.Event)}
    (hc : (sum E F).toGES.isConf c) : E.toGES.isConf {z | Sum.inl z ∈ c} := by sorry
