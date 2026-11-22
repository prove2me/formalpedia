-- Prove2me | Theorems.Thm_CCS_enables_projL
-- name    : CCS.enables_projL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:52:50.269942+00:00
-- url     : https://prove2.me/theorems/c4a3cb34-1bad-4100-a6a9-e363095b192a
-- title:
--   CCS: enables proj L
-- statement:
--   Firing a tag fires an enabled, fresh event of each component it consumes.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L348-L364
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean#L348-L364

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

theorem CCS.enables_projL {t : Tag E F} {x : E.Event}
    (hins : (parSES E F).toGES.isConf (c ∪ {t}))
    (hfr : t ∉ c) (hx : t.evL = some x) :
    E.toGES.isConf (projL c ∪ {x}) ∧ x ∉ projL c := by sorry
