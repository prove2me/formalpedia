-- Prove2me | Theorems.Thm_CCS_resid_res
-- name    : CCS.resid_res
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:23.517403+00:00
-- url     : https://prove2.me/theorems/9454ca66-70e1-44d6-a5e4-e5b16f775f23
-- title:
--   CCS: resid res
-- statement:
--   The CCS construction uses the resid res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L61-L63
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L61-L63

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_res {P : Process (Option Name)} (c : Set (semantics (.res P)).Event) :
    resid (.res P) c = .res (resid P (unres c)) := by sorry
