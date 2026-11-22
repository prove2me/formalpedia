-- Prove2me | Theorems.Thm_CCS_resid_pre_neg
-- name    : CCS.resid_pre_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:14.494802+00:00
-- url     : https://prove2.me/theorems/d1b7b3ce-ce14-4a01-b799-9cdabeea4012
-- title:
--   CCS: resid pre neg
-- statement:
--   The CCS construction uses the resid pre neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L38-L41
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L38-L41

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_pre_neg {α : Action Name} {P : Process Name}
    {c : Set (semantics (.pre α P)).Event} (h : none ∉ c) :
    resid (.pre α P) c = .pre α P := by sorry
