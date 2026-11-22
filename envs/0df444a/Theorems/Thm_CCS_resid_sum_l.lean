-- Prove2me | Theorems.Thm_CCS_resid_sum_l
-- name    : CCS.resid_sum_l
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:22.875566+00:00
-- url     : https://prove2.me/theorems/3512e198-9aa2-4033-bc07-4f79d4c07515
-- title:
--   CCS: resid sum l
-- statement:
--   The CCS construction uses the resid sum l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L43-L45
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L43-L45

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_sum_l {P Q : Process Name} {c : Set (semantics (.sum P Q)).Event}
    (h : ∃ e, Sum.inl e ∈ c) : resid (.sum P Q) c = resid P {e | Sum.inl e ∈ c} := by sorry
