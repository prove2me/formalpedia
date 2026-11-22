-- Prove2me | Theorems.Thm_CCS_resid_nil
-- name    : CCS.resid_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:10.163151+00:00
-- url     : https://prove2.me/theorems/0bdde2aa-1d34-46eb-aad2-df11921a9c6f
-- title:
--   CCS: resid nil
-- statement:
--   The CCS construction uses the resid nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L30-L31
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L30-L31

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_nil (c : Set (semantics (.nil : Process Name)).Event) :
    resid .nil c = .nil := by sorry

attribute [defeq] CCS.resid_nil
