-- Prove2me | Theorems.Thm_CCS_op_to_den
-- name    : CCS.op_to_den
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:59:36.301944+00:00
-- url     : https://prove2.me/theorems/b735a227-4347-402e-9085-b9ce619ce9ed
-- title:
--   CCS: op to den
-- statement:
--   Soundness: every step of the residual process fires an enabled event.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L194-L338
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L194-L338

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.op_to_den : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (α : Action Name) (Q' : Process Name), (semantics P).toGES.isConf c →
    Step (resid P c) α Q' →
    ∃ e, (semantics P).toGES.isConf (c ∪ {e}) ∧ e ∉ c ∧
      (semantics P).label e = α ∧ Q' = resid P (c ∪ {e})
  := by sorry
