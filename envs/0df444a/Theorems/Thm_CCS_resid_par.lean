-- Prove2me | Theorems.Thm_CCS_resid_par
-- name    : CCS.resid_par
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:25.994829+00:00
-- url     : https://prove2.me/theorems/7f573826-1064-4d21-bb6f-327f993e997e
-- title:
--   CCS: resid par
-- statement:
--   The CCS construction uses the resid par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L57-L59
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L57-L59

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_par {P Q : Process Name} (c : Set (semantics (.par P Q)).Event) :
    resid (.par P Q) c = .par (resid P (projL c)) (resid Q (projR c)) := by sorry
