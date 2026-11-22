-- Prove2me | Theorems.Thm_CCS_projR_isConf
-- name    : CCS.projR_isConf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:31.727972+00:00
-- url     : https://prove2.me/theorems/cdd2a492-e11b-4c12-a940-d3950df5e845
-- title:
--   CCS: proj R is Conf
-- statement:
--   The CCS construction uses the proj R is Conf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L286-L289
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L286-L289

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

theorem CCS.projR_isConf (hc : (parSES E F).toGES.isConf c) : F.toGES.isConf (projR c) := by sorry
