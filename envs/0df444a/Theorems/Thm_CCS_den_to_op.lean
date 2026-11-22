-- Prove2me | Theorems.Thm_CCS_den_to_op
-- name    : CCS.den_to_op
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:59:21.186796+00:00
-- url     : https://prove2.me/theorems/d812dbf9-c6fc-4e5a-b79b-6fc6869ed0e1
-- title:
--   CCS: den to op
-- statement:
--   Completeness: firing an enabled event is a step of the residual process.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L89-L191
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L89-L191

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.den_to_op : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (e : (semantics P).Event), (semantics P).toGES.isConf c →
    (semantics P).toGES.isConf (c ∪ {e}) → e ∉ c →
    Step (resid P c) ((semantics P).label e) (resid P (c ∪ {e}))
  := by sorry
