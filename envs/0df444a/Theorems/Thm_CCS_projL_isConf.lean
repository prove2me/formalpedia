-- Prove2me | Theorems.Thm_CCS_projL_isConf
-- name    : CCS.projL_isConf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:06.582744+00:00
-- url     : https://prove2.me/theorems/09a6365e-682a-4506-a8b8-55737d27ebf8
-- title:
--   CCS: proj L is Conf
-- statement:
--   The left projection of a configuration is a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L281-L284
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L281-L284

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}

theorem CCS.projL_isConf (hc : (parSES E F).toGES.isConf c) : E.toGES.isConf (projL c) := by sorry
