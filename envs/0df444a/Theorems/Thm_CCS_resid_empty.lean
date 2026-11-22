-- Prove2me | Theorems.Thm_CCS_resid_empty
-- name    : CCS.resid_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:54:19.053909+00:00
-- url     : https://prove2.me/theorems/f6ac59c3-a1cc-43e5-8a89-72b9f7a7770f
-- title:
--   CCS: resid empty
-- statement:
--   The CCS construction uses the resid empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L65-L86
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Bisimulation.lean#L65-L86

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}

theorem CCS.resid_empty : ∀ {Name : Type u} (P : Process Name), resid P ∅ = P
  := by sorry
