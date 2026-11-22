-- Prove2me | Theorems.Thm_CCS_isConf_insert_tag
-- name    : CCS.isConf_insert_tag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:53:34.147471+00:00
-- url     : https://prove2.me/theorems/d35485c2-e33a-406f-8932-3a1e211e0297
-- title:
--   CCS: is Conf insert tag
-- statement:
--   A fresh tag whose components are enabled extends a configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L385-L530
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L385-L530

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

theorem CCS.isConf_insert_tag {t : Tag E F} (hc : (parSES E F).toGES.isConf c)
    (hL : ∀ x, t.evL = some x → E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c)
    (hR : ∀ y, t.evR = some y → F.toGES.isConf (projR c ∪ {y}) ∧ y ∉ projR c) :
    (parSES E F).toGES.isConf (c ∪ {t}) := by sorry
