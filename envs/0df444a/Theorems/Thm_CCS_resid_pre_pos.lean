-- Prove2me | Theorems.Thm_CCS_resid_pre_pos
-- name    : CCS.resid_pre_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:55:25.389673+00:00
-- url     : https://prove2.me/theorems/aa3519ab-b37d-4add-8320-eb150042bff2
-- title:
--   CCS: resid pre pos
-- statement:
--   The CCS construction uses the resid pre pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L33-L36
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L33-L36

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_pre_pos {α : Action Name} {P : Process Name}
    {c : Set (semantics (.pre α P)).Event} (h : none ∈ c) :
    resid (.pre α P) c = resid P {e | some e ∈ c} := by sorry
